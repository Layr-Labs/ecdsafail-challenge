//! Conservative support identities for CCX only. An atom denotes a Boolean
//! function at its creation boundary, never a mutable wire or classical bit.
//! Unknown products and oversized expressions get fresh, non-reused atoms.

use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit, NO_BIT};

const ATOM_CAP: usize = 32;

#[derive(Clone, PartialEq, Eq)]
struct Affine {
    constant: bool,
    atoms: Vec<u64>,
}

impl Affine {
    fn constant(value: bool) -> Self {
        Self {
            constant: value,
            atoms: Vec::new(),
        }
    }

    fn is_zero(&self) -> bool {
        !self.constant && self.atoms.is_empty()
    }

    fn is_one(&self) -> bool {
        self.constant && self.atoms.is_empty()
    }

    fn complement(&self) -> Self {
        Self {
            constant: !self.constant,
            atoms: self.atoms.clone(),
        }
    }

    fn complements(&self, other: &Self) -> bool {
        self.constant != other.constant && self.atoms == other.atoms
    }
}

pub(super) enum Rewrite {
    Keep,
    Drop,
    X,
    Cx(QubitId),
}

impl Rewrite {
    pub(super) fn emit(self, op: Op, result: &mut Vec<Op>) {
        match self {
            Rewrite::Keep => result.push(op),
            Rewrite::Drop => {}
            rewrite => {
                let mut replacement = Op::empty();
                replacement.q_target = op.q_target;
                replacement.c_condition = op.c_condition;
                match rewrite {
                    Rewrite::X => replacement.kind = OperationType::X,
                    Rewrite::Cx(control) => {
                        replacement.kind = OperationType::CX;
                        replacement.q_control1 = control;
                    }
                    _ => unreachable!(),
                }
                replacement.validate();
                result.push(replacement);
            }
        }
    }
}

pub(super) struct Support {
    qubits: Vec<Affine>,
    bits: Vec<Affine>,
    base_condition: Affine,
    condition_stack: Vec<Affine>,
    next_atom: u64,
}

impl Support {
    pub(super) fn new(ops: &[Op]) -> Self {
        let (nq, nb, _, registers) = analyze_ops(ops.iter());
        let mut quantum_inputs = vec![false; nq as usize];
        let mut classical_inputs = vec![false; nb as usize];
        for register in registers {
            for slot in register {
                match slot {
                    QubitOrBit::Qubit(q) => quantum_inputs[q.0 as usize] = true,
                    QubitOrBit::Bit(b) => classical_inputs[b.0 as usize] = true,
                }
            }
        }
        let mut state = Self {
            qubits: vec![Affine::constant(false); nq as usize],
            bits: vec![Affine::constant(false); nb as usize],
            base_condition: Affine::constant(true),
            condition_stack: Vec::new(),
            next_atom: 0,
        };
        // Both kinds of ABI slot are unknown. Repeated annotations for one
        // physical slot still describe the same value.
        for (q, input) in quantum_inputs.into_iter().enumerate() {
            if input {
                state.qubits[q] = state.fresh();
            }
        }
        for (b, input) in classical_inputs.into_iter().enumerate() {
            if input {
                state.bits[b] = state.fresh();
            }
        }
        state
    }

    fn fresh(&mut self) -> Affine {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("affine atom identifier overflow");
        Affine {
            constant: false,
            atoms: vec![id],
        }
    }

    fn xor(&mut self, a: &Affine, b: &Affine) -> Affine {
        let mut atoms = Vec::with_capacity(a.atoms.len() + b.atoms.len());
        let (mut i, mut j) = (0, 0);
        while i < a.atoms.len() || j < b.atoms.len() {
            if j == b.atoms.len() || (i < a.atoms.len() && a.atoms[i] < b.atoms[j]) {
                atoms.push(a.atoms[i]);
                i += 1;
            } else if i == a.atoms.len() || b.atoms[j] < a.atoms[i] {
                atoms.push(b.atoms[j]);
                j += 1;
            } else {
                i += 1;
                j += 1;
            }
        }
        if atoms.len() > ATOM_CAP {
            // This fresh atom represents the entire XOR, including its
            // constant. It must not be mistaken for zero or an older atom.
            self.fresh()
        } else {
            Affine {
                constant: a.constant ^ b.constant,
                atoms,
            }
        }
    }

    fn and(&mut self, a: &Affine, b: &Affine) -> Affine {
        if a.is_zero() || b.is_zero() || a.complements(b) {
            Affine::constant(false)
        } else if a.is_one() {
            b.clone()
        } else if b.is_one() || a == b {
            a.clone()
        } else {
            // No product cache: equality of unrelated opaque values is never
            // inferred from a hash or from coincident sampled values.
            self.fresh()
        }
    }

    fn ccx_rewrite(condition: &Affine, a: &Affine, b: &Affine, op: &Op) -> Rewrite {
        if condition.is_zero() || a.is_zero() || b.is_zero() || a.complements(b) {
            Rewrite::Drop
        } else if a.is_one() && b.is_one() {
            Rewrite::X
        } else if a.is_one() {
            Rewrite::Cx(op.q_control2)
        } else if b.is_one() || a == b {
            Rewrite::Cx(op.q_control1)
        } else {
            Rewrite::Keep
        }
    }

    pub(super) fn step(&mut self, op: &Op) -> Rewrite {
        if op.kind == OperationType::PushCondition {
            self.condition_stack.push(self.base_condition.clone());
            // Snapshot the current value, not a reference to the bit slot.
            self.base_condition = self.and(
                &self.base_condition.clone(),
                &self.bits[op.c_condition.0 as usize].clone(),
            );
            return Rewrite::Keep;
        }
        if op.kind == OperationType::PopCondition {
            if let Some(saved) = self.condition_stack.pop() {
                self.base_condition = saved;
            }
            return Rewrite::Keep;
        }

        let mut condition = self.base_condition.clone();
        if op.c_condition != NO_BIT {
            condition = self.and(&condition, &self.bits[op.c_condition.0 as usize].clone());
        }

        match op.kind {
            OperationType::CCX => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let b = self.qubits[op.q_control2.0 as usize].clone();
                let rewrite = Self::ccx_rewrite(&condition, &a, &b, op);
                let product = self.and(&a, &b);
                let toggle = self.and(&condition, &product);
                let target = op.q_target.0 as usize;
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &toggle);
                return rewrite;
            }
            OperationType::CX => {
                let target = op.q_target.0 as usize;
                let toggle = self.and(&condition, &self.qubits[op.q_control1.0 as usize].clone());
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &toggle);
            }
            OperationType::X => {
                let target = op.q_target.0 as usize;
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &condition);
            }
            OperationType::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                let difference = self.xor(&self.qubits[a].clone(), &self.qubits[b].clone());
                let toggle = self.and(&condition, &difference);
                // Both destinations share this same actual conditional delta.
                let left = self.xor(&self.qubits[a].clone(), &toggle);
                let right = self.xor(&self.qubits[b].clone(), &toggle);
                self.qubits[a] = left;
                self.qubits[b] = right;
            }
            OperationType::Hmr => {
                let target = op.q_target.0 as usize;
                let bit = op.c_target.0 as usize;
                let outcome = self.fresh();
                let difference = self.xor(&self.bits[bit].clone(), &outcome);
                let toggle = self.and(&condition, &difference);
                self.bits[bit] = self.xor(&self.bits[bit].clone(), &toggle);
                self.qubits[target] =
                    self.and(&self.qubits[target].clone(), &condition.complement());
            }
            OperationType::R => {
                let target = op.q_target.0 as usize;
                self.qubits[target] =
                    self.and(&self.qubits[target].clone(), &condition.complement());
            }
            OperationType::BitInvert => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self.xor(&self.bits[bit].clone(), &condition);
            }
            OperationType::BitStore0 => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self.and(&self.bits[bit].clone(), &condition.complement());
            }
            OperationType::BitStore1 => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self
                    .and(&self.bits[bit].complement(), &condition.complement())
                    .complement();
            }
            // Phase gates do not alter basis support. Preserve them, resets,
            // classical operations and annotations verbatim in the output.
            OperationType::Z
            | OperationType::CZ
            | OperationType::CCZ
            | OperationType::Neg
            | OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {}
            OperationType::PushCondition | OperationType::PopCondition => unreachable!(),
        }
        Rewrite::Keep
    }
}

/// Derive one pass of exact CCX support identities from this stream's ABI and
/// operations. No saved operation indices, nonce assumptions or legacy passes.
pub(crate) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let mut state = Support::new(&ops);
    let mut result = Vec::with_capacity(ops.len());
    for op in ops {
        state.step(&op).emit(op, &mut result);
    }
    result
}

#[cfg(test)]
#[path = "affine_simplify_tests.rs"]
mod tests;
