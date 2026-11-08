//! Cache an unconditional product on an idle zero wire for a later CCX or CCZ.
//! The first Toffoli can target the carrier for arbitrary original target values.
use crate::circuit::{
    analyze_ops, BitId, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT, NO_QUBIT,
};

const MAX_DISTANCE: u32 = 16384;
#[derive(Clone, Copy, Debug)]
struct Hold {
    start: u32,
    end: u32,
    carrier: u16,
    axis: u8,
}

fn axes(op: &Op, axis: u8) -> (QubitId, QubitId, QubitId) {
    let (a, b, t) = (op.q_control1, op.q_control2, op.q_target);
    match axis {
        0 => (a, b, t),
        1 => (a, t, b),
        2 => (b, t, a),
        _ => unreachable!(),
    }
}
fn key(a: usize, b: usize, width: usize) -> usize {
    a.min(b) * width + a.max(b)
}

struct Availability {
    touch: Vec<u32>,
    write: Vec<u32>,
    zero: Vec<bool>,
}

impl Availability {
    fn observe(&mut self, x: &Op, site: u32, unconditional: bool) {
        let (q, a, b) = (
            x.q_target.0 as usize,
            x.q_control1.0 as usize,
            x.q_control2.0 as usize,
        );
        for id in [x.q_control1, x.q_control2, x.q_target] {
            if id != NO_QUBIT {
                self.touch[id.0 as usize] = site;
            }
        }
        match x.kind {
            K::X => {
                self.write[q] = site;
                self.zero[q] = false;
            }
            K::CX | K::CCX => {
                self.write[q] = site;
                if !self.zero[a] && (x.kind == K::CX || !self.zero[b]) {
                    self.zero[q] = false;
                }
            }
            K::Hmr | K::R => {
                self.write[q] = site;
                if unconditional {
                    self.zero[q] = true;
                }
            }
            K::Swap => {
                self.write[a] = site;
                self.write[q] = site;
                if unconditional {
                    self.zero.swap(a, q);
                } else {
                    let both = self.zero[a] && self.zero[q];
                    self.zero[a] = both;
                    self.zero[q] = both;
                }
            }
            _ => {}
        }
    }
    fn carrier(&self, first: u32, target: QubitId) -> Option<usize> {
        self.zero
            .iter()
            .enumerate()
            .position(|(q, &zero)| zero && self.touch[q] < first && q != target.0 as usize)
    }
}

fn select(ops: &[Op], width: usize, zero: Vec<bool>, budget: usize) -> Vec<Hold> {
    // Positions are one based. Zero records an absent previous Toffoli.
    let mut previous = vec![0u32; width * width];
    let mut state = Availability {
        touch: vec![0; width],
        write: vec![0; width],
        zero,
    };
    let mut depth = 0usize;
    let mut holds = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        if holds.len() == budget {
            break;
        }
        let site = i as u32 + 1;
        let unconditional = depth == 0 && op.c_condition == NO_BIT;
        if unconditional && matches!(op.kind, K::CCX | K::CCZ) {
            let mut used = false;
            let options = if op.kind == K::CCZ { 3 } else { 1 };
            for axis in 0..options {
                let (a, b, t) = axes(op, axis);
                let (a, b) = (a.0 as usize, b.0 as usize);
                let index = key(a, b, width);
                let start = previous[index];
                if start == 0
                    || site - start > MAX_DISTANCE
                    || state.write[a] >= start
                    || state.write[b] >= start
                {
                    continue;
                }
                // Both controls and the original target were touched at start.
                if let Some(w) = state.carrier(start, t) {
                    debug_assert_ne!(w, a);
                    debug_assert_ne!(w, b);
                    holds.push(Hold {
                        start: start - 1,
                        end: site - 1,
                        carrier: w as u16,
                        axis,
                    });
                    previous[index] = 0;
                    state.touch[w] = site;
                    used = true;
                    break;
                }
            }
            if !used && op.kind == K::CCX {
                let (a, b, _) = axes(op, 0);
                previous[key(a.0 as usize, b.0 as usize, width)] = site;
            }
        }
        state.observe(op, site, unconditional);
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth = depth.checked_sub(1).unwrap(),
            _ => {}
        }
    }
    holds
}
pub(super) fn apply(ops: &mut Vec<Op>, reserve: usize) -> (usize, usize, usize) {
    let (nq, nb, _, registers) = analyze_ops(ops.iter());
    assert!(nq > 0 && nq <= u16::MAX as u64 && ops.len() < u32::MAX as usize);
    let w = nq as usize;
    let mut zero = vec![true; w];
    for id in registers.iter().flatten() {
        if let QubitOrBit::Qubit(q) = id {
            zero[q.0 as usize] = false;
        }
    }
    let mask = BitId(nb);
    let n = ops.len();
    let budget = ((ops.capacity() - n).saturating_sub(reserve) / 4).min(n.div_ceil(32));
    let holds = select(ops, w, zero, budget);
    let phases = holds
        .iter()
        .filter(|h| ops[h.end as usize].kind == K::CCZ)
        .count();
    let count = holds.len();
    if count == 0 {
        return (0, 0, nb as usize);
    }
    let mut start_order: Vec<u32> = (0..holds.len() as u32).collect();
    start_order.sort_unstable_by_key(|&j| holds[j as usize].start);
    let (mut starts, mut ends) = (start_order.len(), holds.len());
    let layout = (ops.as_ptr(), ops.capacity());
    let (mut read, mut write) = (n, n + 4 * count);
    ops.resize(write, Op::empty());
    while starts != 0 || ends != 0 {
        let start = starts
            .checked_sub(1)
            .map(|i| holds[start_order[i] as usize]);
        let end = ends.checked_sub(1).map(|i| holds[i]);
        let opening = start.is_some() && (end.is_none() || start.unwrap().start > end.unwrap().end);
        let (h, index) = if opening {
            let h = start.unwrap();
            (h, h.start as usize)
        } else {
            let h = end.unwrap();
            (h, h.end as usize)
        };
        let span = read - index - 1;
        if span != 0 {
            ops.copy_within(index + 1..read, write - span);
        }
        write -= span;
        let original = ops[index];
        let carrier = QubitId(h.carrier as u64);
        if opening {
            starts -= 1;
            write -= 2;
            ops[write] = Op {
                q_target: carrier,
                ..original
            };
            ops[write + 1] = Op {
                kind: K::CX,
                q_control1: carrier,
                q_target: original.q_target,
                ..Op::empty()
            };
        } else {
            ends -= 1;
            write -= 4;
            let (a, b, t) = axes(&original, h.axis);
            ops[write] = Op {
                kind: if original.kind == K::CCZ {
                    K::CZ
                } else {
                    K::CX
                },
                q_control1: carrier,
                q_target: t,
                ..Op::empty()
            };
            ops[write + 1] = Op {
                kind: K::Hmr,
                q_target: carrier,
                c_target: mask,
                ..Op::empty()
            };
            ops[write + 2] = Op {
                kind: K::CZ,
                q_control1: a,
                q_target: b,
                c_condition: mask,
                ..Op::empty()
            };
            ops[write + 3] = Op {
                kind: K::BitStore0,
                c_target: mask,
                ..Op::empty()
            };
        }
        read = index;
    }
    assert_eq!(read, write);
    assert_eq!(layout, (ops.as_ptr(), ops.capacity()));
    (count, phases, nb as usize)
}
