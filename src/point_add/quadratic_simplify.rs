//! Degree-two Boolean support identities, combined with the original affine pass.
//! Monomials are canonical square-free pairs: (i,i) means atom i, (i,j)
//! means their product. Atoms denote fixed functions, never mutable slots.
//! An unsupported product or >32 monomials becomes one fresh whole-value atom.

use crate::circuit::{analyze_ops, Op, OperationType, QubitOrBit, NO_BIT};

const MONOMIAL_CAP: usize = 32;

#[derive(Clone, PartialEq, Eq)]
struct Quadratic {
    constant: bool,
    atoms: Vec<(u64, u64)>,
}

impl Quadratic {
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

use super::affine_simplify::{Rewrite, Support as AffineSupport};
use std::collections::BTreeSet;

pub(super) struct Support {
    qubits: Vec<Quadratic>,
    bits: Vec<Quadratic>,
    base_condition: Quadratic,
    condition_stack: Vec<Quadratic>,
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
            qubits: vec![Quadratic::constant(false); nq as usize],
            bits: vec![Quadratic::constant(false); nb as usize],
            base_condition: Quadratic::constant(true),
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

    fn fresh(&mut self) -> Quadratic {
        let id = self.next_atom;
        self.next_atom = id
            .checked_add(1)
            .expect("quadratic atom identifier overflow");
        Quadratic {
            constant: false,
            atoms: vec![(id, id)],
        }
    }

    fn xor(&mut self, a: &Quadratic, b: &Quadratic) -> Quadratic {
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
        if atoms.len() > MONOMIAL_CAP {
            // This fresh atom represents the entire XOR, including its
            // constant. It must not be mistaken for zero or an older atom.
            self.fresh()
        } else {
            Quadratic {
                constant: a.constant ^ b.constant,
                atoms,
            }
        }
    }

    fn and(&mut self, a: &Quadratic, b: &Quadratic) -> Quadratic {
        if a.is_zero() || b.is_zero() || a.complements(b) {
            return Quadratic::constant(false);
        }
        if a.is_one() {
            return b.clone();
        }
        if b.is_one() || a == b {
            return a.clone();
        }
        let mut terms = BTreeSet::new();
        let toggle = |terms: &mut BTreeSet<(u64, u64)>, term| {
            if !terms.insert(term) {
                terms.remove(&term);
            }
        };
        if a.constant {
            for &term in &b.atoms {
                toggle(&mut terms, term);
            }
        }
        if b.constant {
            for &term in &a.atoms {
                toggle(&mut terms, term);
            }
        }
        for &(a0, a1) in &a.atoms {
            for &(b0, b1) in &b.atoms {
                let mut ids = [a0, a1, b0, b1];
                ids.sort_unstable();
                let mut unique = [0; 4];
                let mut count = 0;
                for id in ids {
                    if count == 0 || unique[count - 1] != id {
                        unique[count] = id;
                        count += 1;
                    }
                }
                // Even if later terms could cancel this cubic, forgetting the
                // whole product is conservative. Never drop just that term.
                if count > 2 {
                    return self.fresh();
                }
                toggle(&mut terms, (unique[0], unique[count - 1]));
            }
        }
        if terms.len() > MONOMIAL_CAP {
            return self.fresh();
        }
        Quadratic {
            constant: a.constant && b.constant,
            atoms: terms.into_iter().collect(),
        }
    }

    fn ccx_rewrite(condition: &Quadratic, a: &Quadratic, b: &Quadratic, op: &Op) -> Rewrite {
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

/// Each interpreter sees every original operation, including operations that
/// the output omits. Neither proof state consumes the other's rewritten stream.
pub(crate) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let mut affine = AffineSupport::new(&ops);
    let mut quadratic = Support::new(&ops);
    let mut result = Vec::with_capacity(ops.len());
    for op in ops {
        let affine_rewrite = affine.step(&op);
        let quadratic_rewrite = quadratic.step(&op);
        let rewrite = match affine_rewrite {
            Rewrite::Keep => quadratic_rewrite,
            proven => proven,
        };
        rewrite.emit(op, &mut result);
    }
    result
}

#[cfg(test)]
#[path = "quadratic_simplify_tests.rs"]
mod tests;
