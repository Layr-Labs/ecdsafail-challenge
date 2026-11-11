//! Remove Toffolis that only prepare a wire for an unconditional reset.
//!
//! A run starts with an unconditional CCX writing a wire and continues while
//! that wire is only written. If an unconditional reset follows before any
//! read, the run is measured in the X basis instead. Each write becomes the
//! phase twin of the same boolean condition. The outgoing state and phase are
//! then identical on every input, while the unconditional Toffolis disappear.

use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

pub(super) const Y33_CLEARS: bool = true;
pub(super) const Y33_KEEP_R: bool = false;
pub(super) const Y33_FAULT: Option<(usize, usize)> = None;

struct Site {
    q: u64,
    run: Vec<usize>,
    release: usize,
}

fn find(ops: &[Op]) -> Vec<Site> {
    let mut run: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut depth = 0usize;
    let mut sites = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        let plain = depth == 0 && op.c_condition == NO_BIT;
        let t = op.q_target.0;
        match op.kind {
            OperationType::CX | OperationType::X | OperationType::CCX => {
                if op.kind != OperationType::X {
                    run.remove(&op.q_control1.0);
                }
                if op.kind == OperationType::CCX {
                    run.remove(&op.q_control2.0);
                }
                if !plain {
                    run.remove(&t);
                } else if let Some(r) = run.get_mut(&t) {
                    r.push(i);
                } else if op.kind == OperationType::CCX {
                    run.insert(t, vec![i]);
                }
            }
            OperationType::R => {
                if let Some(r) = run.remove(&t) {
                    if plain {
                        sites.push(Site { q: t, run: r, release: i });
                    }
                }
            }
            OperationType::PushCondition => depth += 1,
            OperationType::PopCondition => depth -= 1,
            OperationType::Neg
            | OperationType::BitInvert
            | OperationType::BitStore0
            | OperationType::BitStore1 => {}
            _ => {
                for q in [op.q_control2, op.q_control1, op.q_target] {
                    if q != NO_QUBIT {
                        run.remove(&q.0);
                    }
                }
            }
        }
    }
    sites
}

fn twin(op: &Op, m: BitId) -> Op {
    let mut z = Op::empty();
    z.c_condition = m;
    match op.kind {
        OperationType::CCX => {
            z.kind = OperationType::CZ;
            z.q_control1 = op.q_control1;
            z.q_target = op.q_control2;
        }
        OperationType::CX => {
            z.kind = OperationType::Z;
            z.q_target = op.q_control1;
        }
        OperationType::X => z.kind = OperationType::Neg,
        k => panic!("y33: {k:?} in a run"),
    }
    z
}

pub(super) fn sweep(ops: &mut Vec<Op>, next_bit: &mut u32) -> (usize, usize) {
    let sites = find(ops);
    let mut act: HashMap<usize, (usize, Option<usize>)> = HashMap::new();
    let mut toffoli = 0;
    for (k, s) in sites.iter().enumerate() {
        let n = s
            .run
            .iter()
            .filter(|&&j| ops[j].kind == OperationType::CCX)
            .count();
        toffoli += n;
        eprintln!(
            "Y33_SITE {k} q={} first={} release={} gates={} toffoli={n}",
            s.q,
            s.run[0],
            s.release,
            s.run.len()
        );
        for (g, &j) in s.run.iter().enumerate() {
            act.insert(j, (k, Some(g)));
        }
        act.insert(s.release, (k, None));
    }
    let old = std::mem::take(ops);
    ops.reserve(old.len() + sites.len());
    for (i, op) in old.into_iter().enumerate() {
        let Some(&(k, g)) = act.get(&i) else {
            ops.push(op);
            continue;
        };
        let m = BitId(u64::from(*next_bit) + k as u64);
        match g {
            None => {
                if Y33_KEEP_R {
                    ops.push(op);
                }
            }
            Some(g) => {
                if g == 0 {
                    let mut h = Op::empty();
                    h.kind = OperationType::Hmr;
                    h.q_target = QubitId(sites[k].q);
                    h.c_target = m;
                    ops.push(h);
                }
                if Y33_FAULT != Some((k, g)) {
                    ops.push(twin(&op, m));
                }
            }
        }
    }
    *next_bit += u32::try_from(sites.len()).expect("site count fits in u32");
    (sites.len(), toffoli)
}
