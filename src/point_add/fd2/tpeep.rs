//! FD: streaming port of tpeep (wt-ra650 construction/codec/tpeep.c, credited 5909718a): delete pairs of identical
//! unconditioned X / CX / CCX when every live record between them commutes with them. Rules (as tpeep):
//!   X-type gates g, h commute iff target(g) not in controls(h) and target(h) not in controls(g);
//!   Z(q), CZ(q1, q2): diagonal, block a candidate iff its target is q / q1 / q2;
//!   HMR(q), R(q): block any candidate touching q;
//!   classically controlled X / CX / CCX: block like the gate, never matched;
//!   classical-only ops (bit invert / store): transparent;
//!   everything else (Swap, condition stack, CCZ, registers, ...): full barrier.
//! The search looks back over at most W live records. Ops wait in a bounded queue so the earlier op of a pair can
//! still be dropped; a live record whose op has left the queue is dropped from the search first.
use crate::circuit::{Op, OperationType as K, NO_BIT, NO_QUBIT};
use std::collections::VecDeque;

const QCAP: usize = 1 << 20;
const E: u64 = u64::MAX;

#[derive(Clone, Copy)]
struct Live {
    key: (u64, u64, u64),
    t: u64,
    a: u64,
    b: u64,
    kind: u8, // 0 gate, 1 diagonal (t, a), 2 measurement / reset (t), 3 never-matching gate
    idx: u64,
}

pub struct TPeep {
    w: usize,
    q: VecDeque<Option<Op>>,
    base: u64,
    live: VecDeque<Live>,
    pub removed_ccx: u64,
    pub removed_other: u64,
}

fn qv(q: crate::circuit::QubitId) -> u64 {
    if q == NO_QUBIT { E } else { q.0 }
}

impl TPeep {
    pub fn new(w: usize) -> TPeep {
        TPeep { w, q: VecDeque::new(), base: 0, live: VecDeque::new(), removed_ccx: 0, removed_other: 0 }
    }

    /// Feed one op; ops leaving the queue are passed to `out` in order.
    pub fn push(&mut self, op: Op, out: &mut dyn FnMut(Op)) {
        let idx = self.base + self.q.len() as u64;
        let cond = op.c_condition != NO_BIT;
        let (mut a, mut b, t) = (qv(op.q_control1), qv(op.q_control2), qv(op.q_target));
        let (gate, blk): (bool, u8) = match op.kind {
            K::X => { a = E; b = E; (!cond, 3) }
            K::CX => { b = E; (!cond, 3) }
            K::CCX => { if b < a { std::mem::swap(&mut a, &mut b); } (!cond, 3) }
            K::Z => { a = E; b = E; (false, 1) }
            K::CZ => { b = E; (false, 1) }
            K::Hmr | K::R => { a = E; b = E; (false, 2) }
            K::BitInvert | K::BitStore0 | K::BitStore1 => { self.enqueue(Some(op), out); return; }
            _ => { self.live.clear(); self.enqueue(Some(op), out); return; }
        };
        if gate {
            let key = (a, b, t);
            let mut hit = None;
            let mut steps = 0usize;
            for j in (0..self.live.len()).rev() {
                if steps >= self.w { break; }
                steps += 1;
                let y = self.live[j];
                if y.kind == 0 && y.key == key { hit = Some(j); break; }
                match y.kind {
                    0 | 3 => { if y.t == a || y.t == b || t == y.a || t == y.b { break; } }
                    1 => { if t == y.t || t == y.a { break; } }
                    _ => { if t == y.t || a == y.t || b == y.t { break; } }
                }
            }
            if let Some(j) = hit {
                let y = self.live.remove(j).unwrap();
                let slot = (y.idx - self.base) as usize;
                debug_assert!(self.q[slot].is_some());
                self.q[slot] = None;
                if op.kind == K::CCX { self.removed_ccx += 2; } else { self.removed_other += 2; }
                return;
            }
            self.push_live(Live { key, t, a, b, kind: 0, idx });
        } else {
            self.push_live(Live { key: (E, E, E), t, a, b, kind: blk, idx });
        }
        self.enqueue(Some(op), out);
    }

    fn push_live(&mut self, l: Live) {
        if self.live.len() >= 4 * self.w + 16 {
            let keep = 2 * self.w;
            let drop = self.live.len() - keep;
            self.live.drain(..drop);
        }
        self.live.push_back(l);
    }

    fn enqueue(&mut self, op: Option<Op>, out: &mut dyn FnMut(Op)) {
        self.q.push_back(op);
        while self.q.len() > QCAP { self.pop_front(out); }
    }

    fn pop_front(&mut self, out: &mut dyn FnMut(Op)) {
        if let Some(o) = self.q.pop_front() {
            self.base += 1;
            while let Some(l) = self.live.front() { if l.idx < self.base { self.live.pop_front(); } else { break; } }
            if let Some(op) = o { out(op); }
        }
    }

    /// Emit everything still queued (end of the circuit).
    pub fn flush(&mut self, out: &mut dyn FnMut(Op)) {
        while !self.q.is_empty() { self.pop_front(out); }
        self.live.clear();
    }
}
