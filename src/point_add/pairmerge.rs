//! lyc-841 pairmerge (commuting Toffoli merge, exact): CCX(a, b, t) at i and CCX(a, c, t) at j > i, both unconditional at
//! condition depth 0, where every op between them commutes with the first. Then CCX(a,b,t) CCX(a,c,t) = X^(a (b ^ c)) on t,
//! emitted at j as CX(c -> b) CCX(a, b, t) CX(c -> b); the op at i is deleted. Chains keep a parity set S of second
//! controls: CCX(a, XOR(S), t), emitted as CX(s -> s0) for s in S \ {s0}, CCX(a, s0, t), the CXs undone; S empty = the
//! merged Toffolis cancel (nothing emitted).
//!
//! Commutation of an op with a pending CCX(a, XOR(S), t) (a quantum statement; a classically conditioned op commutes when
//! its unconditioned form does, so conditions only matter for the two merged CCXs themselves):
//! - an X-type write (X, CX, CCX target) into t commutes (X on t under controls that are not t);
//! - a control read or a diagonal phase (Z, CZ, CCZ) on a or on s in S commutes;
//! - anything else on a, S or t ends the pending item: an X-type write into a or s, a control read of t, a phase on t,
//!   SWAP, HMR, R, or any other op kind naming the wire.
//! A merge needs the new CCX's target t, a shared control a, and its other control c not in {t}.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

struct Item {
    pos: usize,          // op index of the latest merged CCX (the emission point)
    first: [u64; 2],     // the first CCX's two controls (shared control unresolved until the first merge)
    a: u64,              // shared control after the first merge (u64::MAX before)
    s: Vec<u64>,         // parity set of second controls (after the first merge)
    t: u64,
    merged: Vec<usize>,  // indices of all merged CCXs (pos included)
    alive: bool,
}

fn q(x: QubitId) -> Option<u64> { if x == NO_QUBIT { None } else { Some(x.0) } }

pub fn run(ops: Vec<Op>) -> Vec<Op> {
    let mut items: Vec<Item> = Vec::new();
    let mut by_ctrl: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut by_tgt: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut depth = 0usize;
    let mut done: Vec<usize> = Vec::new(); // finalized items with merges
    let kill = |items: &mut Vec<Item>, id: usize, done: &mut Vec<usize>| {
        if items[id].alive { items[id].alive = false; if items[id].merged.len() > 1 { done.push(id); } }
    };
    for (k, op) in ops.iter().enumerate() {
        match op.kind {
            K::PushCondition => { depth += 1; continue; }
            K::PopCondition => { depth -= 1; continue; }
            _ => {}
        }
        let (c1, c2, tg) = (q(op.q_control1), q(op.q_control2), q(op.q_target));
        // classify the op's touches: (wire, role) role 0 = X-write target, 1 = control read, 2 = diagonal phase, 3 = other
        let mut touch: Vec<(u64, u8)> = Vec::with_capacity(3);
        match op.kind {
            K::X => { if let Some(t) = tg { touch.push((t, 0)); } }
            K::CX => { if let Some(c) = c1 { touch.push((c, 1)); } if let Some(t) = tg { touch.push((t, 0)); } }
            K::CCX => { for c in [c1, c2].into_iter().flatten() { touch.push((c, 1)); } if let Some(t) = tg { touch.push((t, 0)); } }
            K::Z | K::CZ | K::CCZ => { for w in [c1, c2, tg].into_iter().flatten() { touch.push((w, 2)); } }
            _ => { for w in [c1, c2, tg].into_iter().flatten() { touch.push((w, 3)); } }
        }
        let plain_ccx = op.kind == K::CCX && depth == 0 && op.c_condition == NO_BIT;
        // 1. merge: a plain CCX into t with a live item on t sharing a control
        let mut merged_into: Option<usize> = None;
        if plain_ccx {
            let (x, y, t) = (c1.unwrap(), c2.unwrap(), tg.unwrap());
            if let Some(ids) = by_tgt.get(&t) {
                for &id in ids.iter().rev() {
                    let it = &items[id];
                    if !it.alive || it.t != t { continue; }
                    // shared control
                    let (a, c) = if it.a == u64::MAX {
                        let f = it.first;
                        if f.contains(&x) && !(f.contains(&y)) { (x, y) } else if f.contains(&y) && !(f.contains(&x)) { (y, x) } else { continue; }
                    } else if x == it.a && y != it.a { (x, y) } else if y == it.a && x != it.a { (y, x) } else { continue; };
                    if c == t || a == t { continue; }
                    merged_into = Some(id);
                    let it = &mut items[id];
                    if it.a == u64::MAX {
                        let other = if it.first[0] == a { it.first[1] } else { it.first[0] };
                        it.a = a; it.s = vec![other];
                    }
                    if let Some(p) = it.s.iter().position(|&w| w == c) { it.s.remove(p); } else { it.s.push(c); }
                    it.pos = k; it.merged.push(k);
                    by_ctrl.entry(c).or_default().push(id);
                    break;
                }
            }
        }
        // 2. invalidate items that do not commute with this op (the merged item itself is exempt for this op)
        for &(w, role) in &touch {
            if role != 1 && role != 2 {
                // X-write into w (role 0) or other (3): items with w as a control end
                if let Some(ids) = by_ctrl.get(&w) {
                    for &id in ids { if Some(id) == merged_into { continue; }
                        let it = &items[id];
                        if it.alive && (it.a == w || it.s.contains(&w) || (it.a == u64::MAX && it.first.contains(&w))) { kill(&mut items, id, &mut done); } }
                }
            }
            if role != 0 {
                // control read (1), phase (2) or other (3) on w: items with target w end
                if let Some(ids) = by_tgt.get(&w) {
                    for &id in ids { if Some(id) == merged_into { continue; } if items[id].alive && items[id].t == w { kill(&mut items, id, &mut done); } }
                }
            }
        }
        // 3. a plain CCX that did not merge opens a new item
        if plain_ccx && merged_into.is_none() {
            let (x, y, t) = (c1.unwrap(), c2.unwrap(), tg.unwrap());
            let id = items.len();
            items.push(Item { pos: k, first: [x, y], a: u64::MAX, s: vec![], t, merged: vec![k], alive: true });
            by_ctrl.entry(x).or_default().push(id);
            by_ctrl.entry(y).or_default().push(id);
            by_tgt.entry(t).or_default().push(id);
        }
        // memory: prune dead ids from the touched lists now and then
        if k % 65536 == 0 {
            by_ctrl.retain(|_, v| { v.retain(|&id| items[id].alive); !v.is_empty() });
            by_tgt.retain(|_, v| { v.retain(|&id| items[id].alive); !v.is_empty() });
        }
    }
    for id in 0..items.len() { if items[id].alive { items[id].alive = false; if items[id].merged.len() > 1 { done.push(id); } } }
    // rewrite
    let mut delete: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut replace: HashMap<usize, Vec<Op>> = HashMap::new();
    let (mut saved, mut cancels) = (0usize, 0usize);
    for &id in &done {
        let it = &items[id];
        for &m in &it.merged { if m != it.pos { delete.insert(m); } }
        let mut seq: Vec<Op> = Vec::new();
        let mk = |kind: K, c1: u64, c2: u64, t: u64| { let mut o = Op::empty(); o.kind = kind; o.q_control1 = QubitId(c1);
            if c2 != u64::MAX { o.q_control2 = QubitId(c2); } o.q_target = QubitId(t); o.validate(); o };
        if it.s.is_empty() {
            cancels += 1; saved += it.merged.len();
        } else {
            let s0 = it.s[0];
            for &s in &it.s[1..] { seq.push(mk(K::CX, s, u64::MAX, s0)); }
            seq.push(mk(K::CCX, it.a, s0, it.t));
            for &s in it.s[1..].iter().rev() { seq.push(mk(K::CX, s, u64::MAX, s0)); }
            saved += it.merged.len() - 1;
        }
        replace.insert(it.pos, seq);
    }
    let _ = NO_BIT;
    let mut out = Vec::with_capacity(ops.len());
    for (k, op) in ops.into_iter().enumerate() {
        if delete.contains(&k) { continue; }
        if let Some(seq) = replace.remove(&k) { out.extend(seq); } else { out.push(op); }
    }
    eprintln!("PAIRMERGE items_merged={} cancels={} toffoli_saved={}", done.len(), cancels, saved);
    out
}
