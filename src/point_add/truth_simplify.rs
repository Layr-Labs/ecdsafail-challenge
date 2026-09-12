//! Exact Boolean tables over at most six immutable value atoms.
//! Tables retain only essential variables. An unsupported union of supports
//! becomes one fresh atom for the WHOLE result, including any constant term.
//! Atom functions can be correlated; universal Boolean identities remain valid.

use super::affine_simplify::{Rewrite, Support as AffineSupport};
use super::quadratic_simplify::Support as QuadraticSupport;
use crate::circuit::{analyze_ops, Op, OperationType, QubitOrBit, NO_BIT};

const SUPPORT_CAP: usize = 6;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Truth {
    // Sorted immutable atom IDs. Bit j of a table row assigns atoms[j].
    atoms: Vec<u64>,
    table: u64,
}

impl Truth {
    fn row_mask(count: usize) -> u64 {
        assert!(count <= SUPPORT_CAP);
        if count == SUPPORT_CAP {
            u64::MAX
        } else {
            (1u64 << (1usize << count)) - 1
        }
    }

    fn constant(value: bool) -> Self {
        Self {
            atoms: Vec::new(),
            table: u64::from(value),
        }
    }

    fn is_zero(&self) -> bool {
        self.atoms.is_empty() && self.table == 0
    }
    fn is_one(&self) -> bool {
        self.atoms.is_empty() && self.table == 1
    }

    fn complement(&self) -> Self {
        Self {
            atoms: self.atoms.clone(),
            table: self.table ^ Self::row_mask(self.atoms.len()),
        }
    }

    fn complements(&self, other: &Self) -> bool {
        self.atoms == other.atoms && self.table ^ other.table == Self::row_mask(self.atoms.len())
    }

    fn canonical(mut atoms: Vec<u64>, mut table: u64) -> Self {
        assert!(atoms.len() <= SUPPORT_CAP);
        assert!(atoms.windows(2).all(|pair| pair[0] < pair[1]));
        table &= Self::row_mask(atoms.len());
        let mut position = 0;
        while position < atoms.len() {
            let bit = 1usize << position;
            let essential = (0..1usize << atoms.len())
                .any(|row| row & bit == 0 && ((table >> row) ^ (table >> (row | bit))) & 1 != 0);
            if essential {
                position += 1;
                continue;
            }
            // Both cofactors agree. Keep the zero cofactor and close the gap
            // in row indexing; the next atom now occupies this same position.
            let mut reduced = 0;
            for row in 0..1usize << (atoms.len() - 1) {
                let original_row = (row & (bit - 1)) | ((row & !(bit - 1)) << 1);
                reduced |= ((table >> original_row) & 1) << row;
            }
            atoms.remove(position);
            table = reduced;
        }
        Self { atoms, table }
    }

    fn value_in_union(&self, positions: &[usize], row: usize) -> u64 {
        let mut own_row = 0;
        for (own_bit, &union_bit) in positions.iter().enumerate() {
            own_row |= ((row >> union_bit) & 1) << own_bit;
        }
        (self.table >> own_row) & 1
    }
}

struct Support {
    qubits: Vec<Truth>,
    bits: Vec<Truth>,
    base_condition: Truth,
    condition_stack: Vec<Truth>,
    next_atom: u64,
}

impl Support {
    fn new(ops: &[Op]) -> Self {
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
            qubits: vec![Truth::constant(false); nq as usize],
            bits: vec![Truth::constant(false); nb as usize],
            base_condition: Truth::constant(true),
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

    fn fresh(&mut self) -> Truth {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("truth atom identifier overflow");
        Truth {
            atoms: vec![id],
            table: 2,
        }
    }

    fn combine(&mut self, a: &Truth, b: &Truth, is_and: bool) -> Truth {
        let mut atoms = a.atoms.clone();
        atoms.extend(&b.atoms);
        atoms.sort_unstable();
        atoms.dedup();
        if atoms.len() > SUPPORT_CAP {
            // Do not retain a partial table or constant. Even two identical
            // unsupported computations get distinct atoms unless copied.
            return self.fresh();
        }
        let positions = |value: &Truth| {
            value
                .atoms
                .iter()
                .map(|id| atoms.binary_search(id).unwrap())
                .collect::<Vec<_>>()
        };
        let a_positions = positions(a);
        let b_positions = positions(b);
        let mut table = 0;
        for row in 0..1usize << atoms.len() {
            let left = a.value_in_union(&a_positions, row);
            let right = b.value_in_union(&b_positions, row);
            let value = if is_and { left & right } else { left ^ right };
            table |= value << row;
        }
        Truth::canonical(atoms, table)
    }

    fn xor(&mut self, a: &Truth, b: &Truth) -> Truth {
        if a == b {
            return Truth::constant(false);
        }
        if a.is_zero() {
            return b.clone();
        }
        if b.is_zero() {
            return a.clone();
        }
        if a.is_one() {
            return b.complement();
        }
        if b.is_one() {
            return a.complement();
        }
        self.combine(a, b, false)
    }

    fn and(&mut self, a: &Truth, b: &Truth) -> Truth {
        if a.is_zero() || b.is_zero() || a.complements(b) {
            return Truth::constant(false);
        }
        if a.is_one() {
            return b.clone();
        }
        if b.is_one() || a == b {
            return a.clone();
        }
        self.combine(a, b, true)
    }

    fn ccx_rewrite(condition: &Truth, a: &Truth, b: &Truth, op: &Op) -> Rewrite {
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

    fn step(&mut self, op: &Op) -> Rewrite {
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

/// All three states consume each ORIGINAL operation before selecting a proof.
/// Existing affine/quadratic proofs take precedence, including facts which the
/// six-atom abstraction forgets. No interpreter sees the emitted replacements.
pub(crate) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    simplify_with_products(ops, false)
}

/// Adds the original-op physical-slot product query after all existing proofs.
pub(crate) fn simplify_products(ops: Vec<Op>) -> Vec<Op> {
    simplify_with_products(ops, true)
}

#[path = "product_simplify.rs"]
mod product;

fn simplify_with_products(ops: Vec<Op>, use_products: bool) -> Vec<Op> {
    let mut affine = AffineSupport::new(&ops);
    let mut quadratic = QuadraticSupport::new(&ops);
    let mut truth = Support::new(&ops);
    let mut products = use_products.then(|| product::Index::new(&truth, &ops));
    let mut result = Vec::with_capacity(ops.len());
    for op in ops {
        // Query the pre-op state; remove old keys before truth mutates it.
        let product_hit = products
            .as_mut()
            .and_then(|index| index.before(&truth, &op));
        let affine_rewrite = affine.step(&op);
        let quadratic_rewrite = quadratic.step(&op);
        let truth_rewrite = truth.step(&op);
        if let Some(index) = &mut products {
            index.after(&truth, &op);
        }
        let rewrite = match (affine_rewrite, quadratic_rewrite) {
            (Rewrite::Keep, Rewrite::Keep) => truth_rewrite,
            (Rewrite::Keep, quadratic_proof) => quadratic_proof,
            (affine_proof, _) => affine_proof,
        };
        match (rewrite, product_hit) {
            (Rewrite::Keep, Some(hit)) => hit.emit(op, &mut result),
            (old_proof, _) => old_proof.emit(op, &mut result),
        }
    }
    result
}

#[cfg(test)]
#[path = "truth_simplify_tests.rs"]
mod tests;
