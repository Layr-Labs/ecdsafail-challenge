//! Original circuit builder for the secp256k1 point-addition challenge.
//!
//! Neutral, general-purpose reversible-circuit construction layer written from
//! scratch for this entry. Emits the `Op` stream consumed by the trusted
//! evaluator. No point-addition or field-arithmetic logic lives here — only
//! wire allocation, register declaration, and the primitive gate set
//! (X / CX / CCX, their classically-conditioned forms, and reset).
//!
//! Cost model (from `sim.rs`): X and Z are free; CX/Swap/R are Clifford;
//! only CCX/CCZ are charged as Toffoli, per shot where the classical
//! condition holds. Peak qubits = highest qubit id referenced. So we keep the
//! Toffoli factor low by routing qubit-vs-classical interactions through CX
//! (Clifford) and the qubit factor low by recycling ancilla ids via a free
//! list once they are known to be |0>.

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};

pub struct B {
    pub ops: Vec<Op>,
    next_q: u64,
    next_b: u64,
    next_r: u64,
    free_q: Vec<u64>,
    high_water_q: u64,
}

impl B {
    pub fn new() -> Self {
        B {
            ops: Vec::new(),
            next_q: 0,
            next_b: 0,
            next_r: 0,
            free_q: Vec::new(),
            high_water_q: 0,
        }
    }

    // ---- allocation -------------------------------------------------------

    /// Allocate one qubit, recycling a freed (|0>) id when available.
    pub fn alloc_qubit(&mut self) -> QubitId {
        let id = if let Some(id) = self.free_q.pop() {
            id
        } else {
            let id = self.next_q;
            self.next_q += 1;
            id
        };
        if id + 1 > self.high_water_q {
            self.high_water_q = id + 1;
        }
        QubitId(id)
    }

    pub fn alloc_qubits(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.alloc_qubit()).collect()
    }

    /// Return a qubit to the free list. Caller must guarantee it holds |0>.
    pub fn free(&mut self, q: QubitId) {
        debug_assert!(!self.free_q.contains(&q.0), "double-free of qubit {}", q.0);
        self.free_q.push(q.0);
    }

    pub fn free_all(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }

    pub fn alloc_bit(&mut self) -> BitId {
        let id = self.next_b;
        self.next_b += 1;
        BitId(id)
    }

    pub fn alloc_bits(&mut self, n: usize) -> Vec<BitId> {
        (0..n).map(|_| self.alloc_bit()).collect()
    }

    pub fn peak_qubits(&self) -> u64 {
        self.high_water_q
    }

    // ---- register declaration --------------------------------------------

    fn next_register(&mut self) -> RegisterId {
        let id = self.next_r;
        self.next_r += 1;
        RegisterId(id)
    }

    fn emit(&mut self, o: Op) {
        o.validate();
        self.ops.push(o);
    }

    /// Declare a 256-wide qubit register (used for target_x / target_y).
    pub fn declare_qubit_register(&mut self, qs: &[QubitId]) -> RegisterId {
        let r = self.next_register();
        let mut reg = Op::empty();
        reg.kind = OperationType::Register;
        reg.r_target = r;
        self.emit(reg);
        for &q in qs {
            let mut a = Op::empty();
            a.kind = OperationType::AppendToRegister;
            a.q_target = q;
            a.r_target = r;
            self.emit(a);
        }
        r
    }

    /// Declare a 256-wide classical-bit register (used for offset_x/offset_y).
    pub fn declare_bit_register(&mut self, bs: &[BitId]) -> RegisterId {
        let r = self.next_register();
        let mut reg = Op::empty();
        reg.kind = OperationType::Register;
        reg.r_target = r;
        self.emit(reg);
        for &b in bs {
            let mut a = Op::empty();
            a.kind = OperationType::AppendToRegister;
            a.c_target = b;
            a.r_target = r;
            self.emit(a);
        }
        r
    }

    // ---- gates (permutation only; phase stays clean) ----------------------

    pub fn x(&mut self, t: QubitId) {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = t;
        self.emit(o);
    }

    pub fn cx(&mut self, c: QubitId, t: QubitId) {
        let mut o = Op::empty();
        o.kind = OperationType::CX;
        o.q_control1 = c;
        o.q_target = t;
        self.emit(o);
    }

    pub fn ccx(&mut self, c1: QubitId, c2: QubitId, t: QubitId) {
        let mut o = Op::empty();
        o.kind = OperationType::CCX;
        o.q_control1 = c1;
        o.q_control2 = c2;
        o.q_target = t;
        self.emit(o);
    }

    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        let mut o = Op::empty();
        o.kind = OperationType::Swap;
        o.q_control1 = a;
        o.q_target = b;
        self.emit(o);
    }

    /// Reset a qubit to |0>. Valid (no phase kickback) only on a qubit already
    /// at |0>; used to document/enforce a clean free before id recycling.
    pub fn reset(&mut self, t: QubitId) {
        let mut o = Op::empty();
        o.kind = OperationType::R;
        o.q_target = t;
        self.emit(o);
    }

    // ---- classically-conditioned gates (controlled by an offset bit) ------
    // A CX conditioned on a classical bit is charged as Clifford, not Toffoli,
    // so "add the classical offset" costs no Toffoli.

    pub fn x_if(&mut self, t: QubitId, cond: BitId) {
        debug_assert!(cond != NO_BIT);
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = t;
        o.c_condition = cond;
        self.emit(o);
    }

    pub fn cx_if(&mut self, c: QubitId, t: QubitId, cond: BitId) {
        debug_assert!(cond != NO_BIT);
        let mut o = Op::empty();
        o.kind = OperationType::CX;
        o.q_control1 = c;
        o.q_target = t;
        o.c_condition = cond;
        self.emit(o);
    }

    /// Toffoli with an extra classical condition: fires on qubit controls only
    /// when `cond` holds. Still charged as Toffoli on conditioned shots.
    pub fn ccx_if(&mut self, c1: QubitId, c2: QubitId, t: QubitId, cond: BitId) {
        debug_assert!(cond != NO_BIT);
        let mut o = Op::empty();
        o.kind = OperationType::CCX;
        o.q_control1 = c1;
        o.q_control2 = c2;
        o.q_target = t;
        o.c_condition = cond;
        self.emit(o);
    }
}
