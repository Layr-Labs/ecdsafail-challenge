
use std::collections::HashMap;

use crate::circuit::{Op, OperationType as K, NO_BIT};

const NQW: u64 = u64::MAX;

#[derive(Clone, PartialEq, Eq, Hash)]
struct Key {
    kind: u8,
    w: [u64; 3],
    target: u64,
    cc: u64,
    stack: Vec<u64>,
}

fn is_toffoli(o: &Op) -> bool {
    matches!(o.kind, K::CCX | K::CCZ)
}

fn key_of(o: &Op, stack: &[u64]) -> Key {
    match o.kind {
        K::CCX => {
            let (a, b) = (o.q_control1.0, o.q_control2.0);
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
            Key { kind: o.kind as u8, w: [lo, hi, NQW], target: o.q_target.0,
                  cc: o.c_condition.0, stack: stack.to_vec() }
        }
        K::CCZ => {
            let mut w = [o.q_control1.0, o.q_control2.0, o.q_target.0];
            w.sort_unstable();
            Key { kind: o.kind as u8, w, target: NQW,
                  cc: o.c_condition.0, stack: stack.to_vec() }
        }
        _ => unreachable!(),
    }
}

fn touched_wires(o: &Op, out: &mut [u64; 3]) -> usize {
    let mut n = 0;
    for v in [o.q_control2.0, o.q_control1.0, o.q_target.0] {
        if v != NQW {
            out[n] = v;
            n += 1;
        }
    }
    n
}

fn writes_wire(o: &Op, w: u64) -> bool {
    let t = o.q_target.0;
    match o.kind {
        K::X | K::CX | K::CCX | K::R | K::Hmr => w == t,
        K::Swap => w == t || w == o.q_control1.0 || w == o.q_control2.0,
        K::Neg => w == t || w == o.q_control1.0 || w == o.q_control2.0,
        _ => false,
    }
}

fn quantum_commutes(c_w: &[u64; 3], c_target: u64, o: &Op) -> bool {
    let mut tw = [0u64; 3];
    let tn = touched_wires(o, &mut tw);
    for &w in &tw[..tn] {
        if c_target != NQW && w == c_target {
            return false;
        }
        if c_w.contains(&w) && writes_wire(o, w) {
            return false;
        }
    }
    true
}

fn once(ops: &mut Vec<Op>) -> usize {
    let n = ops.len();
    let mut dead = vec![false; n];
    let mut cand: HashMap<Key, Vec<usize>> = HashMap::new();
    let mut alive = vec![false; n];
    let mut by_wire: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut by_bit: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut meta: HashMap<usize, ([u64; 3], u64)> = HashMap::new();
    let mut stack: Vec<u64> = Vec::new();


    for j in 0..n {
        if dead[j] {
            continue;
        }
        let o = ops[j];
        match o.kind {
            K::PushCondition => {
                stack.push(o.c_condition.0);
                continue;
            }
            K::PopCondition => {
                stack.pop();
                continue;
            }
            _ => {}
        }

        if is_toffoli(&o) {
            let k = key_of(&o, &stack);
            let mut paired = false;
            if let Some(list) = cand.get_mut(&k) {
                while let Some(i) = list.pop() {
                    if alive.get(i).copied().unwrap_or(false) {
                        dead[i] = true;
                        dead[j] = true;
                        alive[i] = false;
                        meta.remove(&i);
                        paired = true;
                        break;
                    }
                }
            }
            if paired {
                continue;
            }
        }

        let mut tw = [0u64; 3];
        let tn = touched_wires(&o, &mut tw);
        for &w in &tw[..tn] {
            if let Some(list) = by_wire.get_mut(&w) {
                list.retain(|&i| {
                    if !alive[i] {
                        return false;
                    }
                    let &(cw, ct) = meta.get(&i).unwrap();
                    if quantum_commutes(&cw, ct, &o) {
                        true
                    } else {
                        alive[i] = false;
                        meta.remove(&i);
                        false
                    }
                });
            }
        }
        if o.c_target != NO_BIT {
            let b = o.c_target.0;
            if let Some(list) = by_bit.get_mut(&b) {
                for &i in list.iter() {
                    alive[i] = false;
                    meta.remove(&i);
                }
                list.clear();
            }
        }

        if is_toffoli(&o) {
            let i = j;
            let k = key_of(&o, &stack);
            let (cw, ct) = (k.w, k.target);
            alive[i] = true;
            meta.insert(i, (cw, ct));
            cand.entry(k.clone()).or_default().push(i);
            for &w in &cw {
                if w != NQW {
                    by_wire.entry(w).or_default().push(i);
                }
            }
            if ct != NQW {
                by_wire.entry(ct).or_default().push(i);
            }
            if k.cc != u64::MAX {
                by_bit.entry(k.cc).or_default().push(i);
            }
            for &b in &k.stack {
                by_bit.entry(b).or_default().push(i);
            }
        }
    }

    let mut out = Vec::with_capacity(n);
    let mut removed = 0usize;
    for (i, o) in ops.drain(..).enumerate() {
        if dead[i] {
            removed += 1;
            continue;
        }
        out.push(o);
    }
    *ops = out;
    removed
}

pub fn run(mut ops: Vec<Op>) -> Vec<Op> {
    for _ in 0..64 {
        let before = ops.len();
        if once(&mut ops) == 0 {
            break;
        }
        eprintln!("tof_cancel: {} ops this round", before - ops.len());
    }
    ops
}
