//! Hold an indicator of a binary affine plane, reusing it in another basis.
use crate::circuit::{
    analyze_ops, BitId, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT, NO_QUBIT,
};
#[path = "basis.rs"]
mod basis;
#[path = "names.rs"]
mod names;
use basis::Plane;
use names::{bucket, Form, Names};
const WINDOW: u32 = 16_384;
#[derive(Clone, Copy)]
struct Hold {
    start: u32,
    end: u32,
    carrier: u16,
    axis: u8,
    flip_a: bool,
    flip_b: bool,
    owns_start: bool,
    erases: bool,
}
impl Hold {
    fn update_terms(self) -> usize {
        usize::from(self.flip_a)
            + usize::from(self.flip_b)
            + usize::from(self.flip_a && self.flip_b)
    }
    fn cleanup_terms(self) -> usize {
        3 + self.update_terms()
    }
    fn end_len(self) -> usize {
        1 + self.update_terms() + if self.erases { self.cleanup_terms() } else { 0 }
    }
}
#[derive(Clone, Copy, Default)]
struct Origin {
    first: Form,
    second: Form,
    start: u32,
    point: u8,
    tail: u32,
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
struct Selector {
    names: Names,
    zero_words: Vec<u64>,
    touched: Vec<u32>,
    previous: Vec<Origin>,
    holds: Vec<Hold>,
    growth: usize,
    limit: usize,
    depth: usize,
}
impl Selector {
    fn new(inputs: &[bool], limit: usize) -> Self {
        let mut s = Self {
            names: Names::new(inputs),
            zero_words: vec![0; inputs.len().div_ceil(64)],
            touched: vec![0; inputs.len()],
            previous: vec![Origin::default(); 1 << 18],
            holds: Vec::new(),
            growth: 0,
            limit,
            depth: 0,
        };
        for i in 0..inputs.len() {
            s.refresh(i);
        }
        s
    }
    fn refresh(&mut self, i: usize) {
        let bit = 1u64 << (i & 63);
        let word = &mut self.zero_words[i >> 6];
        if self.names.wires[i].zero() {
            *word |= bit;
        } else {
            *word &= !bit;
        }
    }
    fn idle(&self, start: u32, op: &Op) -> Option<usize> {
        for (j, &word) in self.zero_words.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let q = 64 * j + bits.trailing_zeros() as usize;
                bits &= bits - 1;
                let id = QubitId(q as u64);
                if self.touched[q] < start
                    && id != op.q_target
                    && id != op.q_control1
                    && id != op.q_control2
                {
                    return Some(q);
                }
            }
        }
        None
    }
    fn pair(&mut self, op: &Op, site: u32) {
        let variants = if op.kind == K::CCZ { 3 } else { 1 };
        let mut origin = None;
        for axis in 0..variants {
            let (a, b, _) = axes(op, axis);
            let Some(p) = Plane::new(
                self.names.wires[a.0 as usize],
                self.names.wires[b.0 as usize],
            ) else {
                continue;
            };
            let i = bucket(p.first, p.second, self.previous.len());
            let last = self.previous[i];
            if op.kind == K::CCX {
                origin = Some((
                    i,
                    Origin {
                        first: p.first,
                        second: p.second,
                        start: site,
                        point: p.active_point(),
                        tail: 0,
                    },
                ));
            }
            if last.start == 0 || last.first != p.first || last.second != p.second {
                continue;
            }
            let (active_a, active_b) = p.values(last.point);
            let prior = last.tail.checked_sub(1).map(|j| j as usize);
            let w = if let Some(j) = prior {
                let tail = self.holds[j];
                let w = tail.carrier as usize;
                let q = QubitId(w as u64);
                if self.touched[w] != tail.end + 1
                    || site - (tail.end + 1) > WINDOW
                    || q == op.q_target
                    || q == op.q_control1
                    || q == op.q_control2
                {
                    continue;
                }
                w
            } else {
                if site - last.start > WINDOW {
                    continue;
                }
                let Some(w) = self.idle(last.start, op) else {
                    continue;
                };
                w
            };
            let h = Hold {
                start: last.start - 1,
                end: site - 1,
                carrier: w as u16,
                axis,
                flip_a: !active_a,
                flip_b: !active_b,
                owns_start: prior.is_none(),
                erases: true,
            };
            let refund = prior.map(|j| self.holds[j].cleanup_terms()).unwrap_or(0);
            let next = self.growth - refund + h.end_len() - 1 + usize::from(h.owns_start);
            if next > self.limit {
                continue;
            }
            if let Some(j) = prior {
                assert!(self.holds[j].erases);
                self.holds[j].erases = false;
            }
            self.growth = next;
            self.holds.push(h);
            self.previous[i].tail = self.holds.len() as u32;
            self.touched[w] = site;
            return;
        }
        if let Some((i, r)) = origin {
            self.previous[i] = r;
        }
    }
    fn run(mut self, ops: &[Op]) -> (Vec<Hold>, usize) {
        for (i, x) in ops.iter().enumerate() {
            let site = i as u32 + 1;
            let un = self.depth == 0 && x.c_condition == NO_BIT;
            if un && matches!(x.kind, K::CCX | K::CCZ) {
                self.pair(x, site);
            }
            for q in [x.q_control1, x.q_control2, x.q_target] {
                if q != NO_QUBIT {
                    self.touched[q.0 as usize] = site;
                }
            }
            self.names.observe(x, un);
            if matches!(x.kind, K::X | K::CX | K::CCX | K::Hmr | K::R | K::Swap) {
                self.refresh(x.q_target.0 as usize);
            }
            if x.kind == K::Swap {
                self.refresh(x.q_control1.0 as usize);
            }
            match x.kind {
                K::PushCondition => self.depth += 1,
                K::PopCondition => self.depth = self.depth.checked_sub(1).unwrap(),
                _ => {}
            }
        }
        (self.holds, self.growth)
    }
}
fn last_gates(h: Hold, source: Op, mask: BitId, out: &mut [Op]) {
    let (a, b, t) = axes(&source, h.axis);
    let w = QubitId(h.carrier as u64);
    let phase = source.kind == K::CCZ;
    let controlled = if phase { K::CZ } else { K::CX };
    let single = if phase { K::Z } else { K::X };
    let mut i = 0;
    let mut push = |x| {
        out[i] = x;
        i += 1;
    };
    let control = |q| Op {
        kind: controlled,
        q_control1: q,
        q_target: t,
        ..Op::empty()
    };
    push(control(w));
    if h.flip_a {
        push(control(b));
    }
    if h.flip_b {
        push(control(a));
    }
    if h.flip_a && h.flip_b {
        push(Op {
            kind: single,
            q_target: t,
            ..Op::empty()
        });
    }
    if !h.erases {
        assert_eq!(i, out.len());
        return;
    }
    push(Op {
        kind: K::Hmr,
        q_target: w,
        c_target: mask,
        ..Op::empty()
    });
    push(Op {
        kind: K::CZ,
        q_control1: a,
        q_target: b,
        c_condition: mask,
        ..Op::empty()
    });
    let z = |q| Op {
        kind: K::Z,
        q_target: q,
        c_condition: mask,
        ..Op::empty()
    };
    if h.flip_a {
        push(z(b));
    }
    if h.flip_b {
        push(z(a));
    }
    if h.flip_a && h.flip_b {
        push(Op {
            kind: K::Neg,
            c_condition: mask,
            ..Op::empty()
        });
    }
    push(Op {
        kind: K::BitStore0,
        c_target: mask,
        ..Op::empty()
    });
    assert_eq!(i, out.len());
}

pub(super) fn apply(ops: &mut Vec<Op>, reserve: usize) -> (usize, usize, usize) {
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let n = ops.len();
    assert!(nq > 0 && nq <= u16::MAX as u64 && n < u32::MAX as usize);
    let mut inputs = vec![false; nq as usize];
    for slot in regs.iter().flatten() {
        if let QubitOrBit::Qubit(q) = slot {
            inputs[q.0 as usize] = true;
        }
    }
    let budget = (ops.capacity() - n)
        .saturating_sub(reserve)
        .min(n.div_ceil(6).max(32));
    let (holds, growth) = Selector::new(&inputs, budget).run(ops);
    let count = holds.len();
    let diag = holds
        .iter()
        .filter(|h| ops[h.end as usize].kind == K::CCZ)
        .count();
    let signed = holds.iter().filter(|h| h.flip_a || h.flip_b).count();
    let grouped = holds.iter().filter(|h| !h.owns_start).count();
    eprintln!("Q659_AFFINE_CHAINS extended={grouped} saved={count} signed={signed} ccz={diag} growth={growth} limit={budget}");
    if count == 0 {
        return (0, 0, nb as usize);
    }
    let mut order: Vec<u32> = (0..count as u32)
        .filter(|&j| holds[j as usize].owns_start)
        .collect();
    order.sort_unstable_by_key(|&j| holds[j as usize].start);
    let (mut starts, mut ends) = (order.len(), count);
    let layout = (ops.as_ptr(), ops.capacity());
    let (mut read, mut write) = (n, n + growth);
    ops.resize(write, Op::empty());
    while starts != 0 || ends != 0 {
        let s = starts.checked_sub(1).map(|i| holds[order[i] as usize]);
        let e = ends.checked_sub(1).map(|i| holds[i]);
        let opening = s.is_some() && (e.is_none() || s.unwrap().start > e.unwrap().end);
        let (h, index) = if opening {
            let h = s.unwrap();
            (h, h.start as usize)
        } else {
            let h = e.unwrap();
            (h, h.end as usize)
        };
        let span = read - index - 1;
        if span != 0 {
            ops.copy_within(index + 1..read, write - span);
        }
        write -= span;
        let old = ops[index];
        let w = QubitId(h.carrier as u64);
        if opening {
            starts -= 1;
            write -= 2;
            ops[write] = Op { q_target: w, ..old };
            ops[write + 1] = Op {
                kind: K::CX,
                q_control1: w,
                q_target: old.q_target,
                ..Op::empty()
            };
        } else {
            ends -= 1;
            let length = h.end_len();
            write -= length;
            last_gates(h, old, BitId(nb), &mut ops[write..write + length]);
        }
        read = index;
    }
    assert_eq!(read, write);
    assert_eq!(layout, (ops.as_ptr(), ops.capacity()));
    (count, diag, nb as usize)
}
