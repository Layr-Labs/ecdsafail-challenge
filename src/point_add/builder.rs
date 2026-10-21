//! froghop-double builder: qubit pool, op emission and a small gate IR that can be emitted forward or inverted.
//!
//! Gates are always emitted through `g()`. While a recording is open, they go to the recording instead of the
//! op stream; `play(rec, inverse)` emits a recording forward or as its exact inverse. The only non-self-inverse
//! gates are the measurement-based AND pair: `AndC` (Toffoli into a fresh |0> target, 1 Toffoli) and `AndU`
//! (X-basis measurement of the target plus a classically conditioned CZ fix-up, 0 Toffoli). They invert into
//! each other.

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT, NO_REG};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G {
    X(QubitId),
    Cx(QubitId, QubitId),
    Ccx(QubitId, QubitId, QubitId),
    Cz(QubitId, QubitId),
    Swap(QubitId, QubitId),
    /// t ^= a & b with t known to be |0> (compute).
    AndC(QubitId, QubitId, QubitId),
    /// t = a & b -> |0> by measurement (uncompute).
    AndU(QubitId, QubitId, QubitId),
    /// X conditioned on a classical bit.
    XIf(QubitId, BitId),
    /// Z conditioned on a classical bit.
    ZIf(QubitId, BitId),
}

pub struct B {
    pub ops: Vec<Op>,
    next_q: u64,
    free_q: BTreeSet<u64>,
    pub live: u64,
    pub peak: u64,
    bit: BitId,
    rec: Vec<Vec<G>>,
    pub tof: u64,
    pub peak_op: usize,
    next_bit: u64,
}

impl B {
    pub fn new() -> Self {
        let mut b = B { ops: Vec::new(), next_q: 0, free_q: BTreeSet::new(), live: 0, peak: 0, bit: NO_BIT,
                        rec: Vec::new(), tof: 0, next_bit: 10_000, peak_op: 0 };
        b.bit = BitId(0);
        b
    }

    // ---------------------------------------------------------------- qubits
    pub fn alloc(&mut self) -> QubitId {
        let id = if let Some(&q) = self.free_q.iter().next() {
            self.free_q.remove(&q);
            q
        } else {
            self.next_q += 1;
            self.next_q - 1
        };
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        QubitId(id)
    }
    pub fn alloc_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.alloc()).collect()
    }
    /// Release a qubit that is |0> on every shot.
    pub fn free(&mut self, q: QubitId) {
        assert!(self.rec.is_empty(), "free inside a recording");
        assert!(self.free_q.insert(q.0), "double free q{}", q.0);
        self.live -= 1;
    }
    pub fn free_n(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    pub fn width(&self) -> u64 {
        self.next_q
    }

    // ---------------------------------------------------------------- registers
    pub fn declare_qubits(&mut self, reg: u64, qs: &[QubitId]) {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        for &q in qs {
            self.raw(Op { kind: OperationType::AppendToRegister, q_target: q, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
    }
    pub fn declare_bits(&mut self, reg: u64, n: usize) -> Vec<BitId> {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        let bs: Vec<BitId> = (0..n).map(|i| BitId(1 + reg * 1000 + i as u64)).collect();
        for &b in &bs {
            self.raw(Op { kind: OperationType::AppendToRegister, c_target: b, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
        bs
    }

    // ---------------------------------------------------------------- emission
    fn raw(&mut self, op: Op) {
        debug_assert!({ op.validate(); true });
        let _ = NO_REG;
        self.ops.push(op);
    }
    fn emit(&mut self, g: G, inverse: bool) {
        let e = |kind, t: QubitId, c1: QubitId, c2: QubitId| Op { kind, q_target: t, q_control1: c1, q_control2: c2,
                                                             ..Op::empty() };
        match g {
            G::X(t) => self.raw(e(OperationType::X, t, NO_QUBIT, NO_QUBIT)),
            G::Cx(c, t) => self.raw(e(OperationType::CX, t, c, NO_QUBIT)),
            G::Cz(a, b) => self.raw(e(OperationType::CZ, b, a, NO_QUBIT)),
            G::Swap(a, b) => self.raw(e(OperationType::Swap, b, a, NO_QUBIT)),
            G::Ccx(a, b, t) => {
                self.tof += 1;
                self.raw(e(OperationType::CCX, t, a, b))
            }
            G::XIf(t, c) => self.raw(Op { kind: OperationType::X, q_target: t, c_condition: c, ..Op::empty() }),
            G::ZIf(t, c) => self.raw(Op { kind: OperationType::Z, q_target: t, c_condition: c, ..Op::empty() }),
            G::AndC(a, b, t) | G::AndU(a, b, t) => {
                let compute = matches!(g, G::AndC(..)) != inverse;
                if compute {
                    self.tof += 1;
                    self.raw(e(OperationType::CCX, t, a, b));
                } else {
                    let m = self.bit;
                    self.raw(Op { kind: OperationType::Hmr, q_target: t, c_target: m, ..Op::empty() });
                    self.raw(Op { kind: OperationType::CZ, q_target: b, q_control1: a, c_condition: m,
                                  ..Op::empty() });
                }
            }
        }
    }
    /// Emit one gate (or record it if a recording is open).
    pub fn g(&mut self, g: G) {
        if let Some(r) = self.rec.last_mut() {
            r.push(g);
        } else {
            self.emit(g, false);
        }
    }
    pub fn begin(&mut self) {
        self.rec.push(Vec::new());
    }
    pub fn end(&mut self) -> Vec<G> {
        self.rec.pop().expect("no recording")
    }
    /// Emit a recording forward or as its inverse (into the enclosing recording if one is open).
    pub fn play(&mut self, r: &[G], inverse: bool) {
        if inverse {
            for &g in r.iter().rev() {
                let gi = match g {
                    G::AndC(a, b, t) => G::AndU(a, b, t),
                    G::AndU(a, b, t) => G::AndC(a, b, t),
                    other => other,
                };
                self.g(gi);
            }
        } else {
            for &g in r {
                self.g(g);
            }
        }
    }

    // ---------------------------------------------------------------- gate helpers
    pub fn x(&mut self, t: QubitId) {
        self.g(G::X(t));
    }
    pub fn cx(&mut self, c: QubitId, t: QubitId) {
        self.g(G::Cx(c, t));
    }
    pub fn ccx(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::Ccx(a, b, t));
    }
    pub fn cz(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Cz(a, b));
    }
    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Swap(a, b));
    }
    pub fn and_c(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndC(a, b, t));
    }
    pub fn and_u(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndU(a, b, t));
    }
    pub fn x_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::XIf(t, c));
    }
    pub fn z_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::ZIf(t, c));
    }
    /// X-basis measurement of q into classical bit c (q -> |0>). Not invertible; never inside a recording.
    pub fn hmr_to(&mut self, q: QubitId, c: BitId) {
        assert!(self.rec.is_empty());
        self.raw(Op { kind: OperationType::Hmr, q_target: q, c_condition: NO_BIT, c_target: c, ..Op::empty() });
    }
    /// Take a specific free qubit back out of the pool.
    pub fn acquire(&mut self, q: QubitId) {
        assert!(self.free_q.remove(&q.0), "acquire of a busy qubit q{}", q.0);
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
    }
    pub fn fresh_bits(&mut self, n: usize) -> Vec<BitId> {
        let v: Vec<BitId> = (0..n).map(|i| BitId(self.next_bit + i as u64)).collect();
        self.next_bit += n as u64;
        v
    }
    /// Controlled swap (Fredkin), 1 Toffoli.
    pub fn cswap(&mut self, c: QubitId, a: QubitId, b: QubitId) {
        self.cx(b, a);
        self.ccx(c, a, b);
        self.cx(b, a);
    }
}
