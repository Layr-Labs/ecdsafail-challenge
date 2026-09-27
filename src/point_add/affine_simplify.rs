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
    ComplementedCx(QubitId),
}

impl Rewrite {
    fn operations(self, op: Op) -> [Option<Op>; 2] {
        let mut replacement = Op::empty();
        replacement.q_target = op.q_target;
        replacement.c_condition = op.c_condition;
        let mut second = None;
        match self {
            Rewrite::Keep => return [Some(op), None],
            Rewrite::Drop => return [None, None],
            Rewrite::X => replacement.kind = OperationType::X,
            Rewrite::Cx(control) => {
                replacement.kind = OperationType::CX;
                replacement.q_control1 = control;
            }
            Rewrite::ComplementedCx(control) => {
                replacement.kind = OperationType::X;
                let mut cx = replacement;
                cx.kind = OperationType::CX;
                cx.q_control1 = control;
                cx.validate();
                second = Some(cx);
            }
        }
        replacement.validate();
        [Some(replacement), second]
    }

    pub(super) fn emit(self, op: Op, result: &mut Vec<Op>) {
        result.extend(self.operations(op).into_iter().flatten());
        #[cfg(test)]
        super::measurement::rewritten_op(result.len());
    }
}

pub(super) fn rewrite_in_place(
    mut ops: Vec<Op>,
    mut rewrite: impl FnMut(&Op) -> Rewrite,
) -> Vec<Op> {
    let mut insertions = Vec::new();
    let (mut retained, mut emitted) = (0, 0);
    ops.retain_mut(|op| {
        let keep = match rewrite(op) {
            Rewrite::Keep => true,
            Rewrite::Drop => false,
            proof => {
                let [first, second] = proof.operations(*op);
                let first = first.expect("non-dropping rewrite has an operation");
                if let Some(second) = second {
                    // Delay expansion so it cannot overwrite an unread original.
                    insertions.push((retained, first));
                    *op = second;
                    emitted += 1;
                } else {
                    *op = first;
                }
                true
            }
        };
        if keep {
            retained += 1;
            emitted += 1;
        }
        #[cfg(test)]
        super::measurement::rewritten_op(emitted);
        keep
    });
    if !insertions.is_empty() {
        ops.resize(emitted, Op::empty());
        let mut insertions = insertions.into_iter().rev().peekable();
        let mut write = emitted;
        for read in (0..retained).rev() {
            write -= 1;
            ops[write] = ops[read];
            if insertions.peek().is_some_and(|(index, _)| *index == read) {
                write -= 1;
                ops[write] = insertions.next().unwrap().1;
            }
        }
        assert_eq!(write, 0);
        assert!(insertions.next().is_none());
    }
    ops
}

pub(super) struct Inputs {
    pub(super) qubits: Vec<bool>,
    pub(super) bits: Vec<bool>,
}

impl Inputs {
    pub(super) fn new(ops: &[Op]) -> Self {
        let (nq, nb, _, registers) = analyze_ops(ops.iter());
        let mut inputs = Self {
            qubits: vec![false; nq as usize],
            bits: vec![false; nb as usize],
        };
        for register in registers {
            for slot in register {
                match slot {
                    QubitOrBit::Qubit(q) => inputs.qubits[q.0 as usize] = true,
                    QubitOrBit::Bit(b) => inputs.bits[b.0 as usize] = true,
                }
            }
        }
        inputs
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
    pub(super) fn new(inputs: &Inputs) -> Self {
        let mut state = Self {
            qubits: vec![Affine::constant(false); inputs.qubits.len()],
            bits: vec![Affine::constant(false); inputs.bits.len()],
            base_condition: Affine::constant(true),
            condition_stack: Vec::new(),
            next_atom: 0,
        };
        // Both kinds of ABI slot are unknown. Repeated annotations for one
        // physical slot still describe the same value.
        for (q, &input) in inputs.qubits.iter().enumerate() {
            if input {
                state.qubits[q] = state.fresh();
            }
        }
        for (b, &input) in inputs.bits.iter().enumerate() {
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
    let mut state = Support::new(&Inputs::new(&ops));
    rewrite_in_place(ops, |op| state.step(op))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId, RegisterId};

    fn input() -> Vec<Op> {
        (2..7)
            .map(|target| {
                let mut op = Op::empty();
                op.kind = OperationType::CCX;
                op.q_control1 = QubitId(0);
                op.q_control2 = QubitId(1);
                op.q_target = QubitId(target);
                if target % 2 == 0 {
                    op.c_condition = BitId(0);
                }
                op
            })
            .collect()
    }

    #[test]
    fn compaction_matches_all_keep_drop_weaken_and_expand_combinations() {
        for mut choices in 0..5usize.pow(5) {
            let original = input();
            let mut expected = Vec::new();
            let mut rewrites = Vec::new();
            for &op in &original {
                let choice = choices % 5;
                choices /= 5;
                let mut x = Op::empty();
                x.kind = OperationType::X;
                x.q_target = op.q_target;
                x.c_condition = op.c_condition;
                let mut cx = x;
                cx.kind = OperationType::CX;
                cx.q_control1 = QubitId(7);
                let rewrite = match choice {
                    0 => {
                        expected.push(op);
                        Rewrite::Keep
                    }
                    1 => Rewrite::Drop,
                    2 => {
                        expected.push(x);
                        Rewrite::X
                    }
                    3 => {
                        expected.push(cx);
                        Rewrite::Cx(QubitId(7))
                    }
                    4 => {
                        expected.extend([x, cx]);
                        Rewrite::ComplementedCx(QubitId(7))
                    }
                    _ => unreachable!(),
                };
                rewrites.push(rewrite);
            }
            let mut rewrites = rewrites.into_iter();
            let result = rewrite_in_place(original, |_| rewrites.next().unwrap());
            assert!(rewrites.next().is_none());
            assert_eq!(result, expected);
            for op in result {
                op.validate();
            }
        }
    }

    #[test]
    fn nonexpanding_rewrites_reuse_the_input_allocation() {
        let original = input();
        let pointer = original.as_ptr();
        let capacity = original.capacity();
        let result = rewrite_in_place(original, |op| {
            if op.q_target.0 % 2 == 0 {
                Rewrite::Drop
            } else {
                Rewrite::X
            }
        });
        assert_eq!(result.len(), 2);
        assert_eq!(result.as_ptr(), pointer);
        assert_eq!(result.capacity(), capacity);
        assert!(result.iter().all(|op| op.kind == OperationType::X));

        let result = rewrite_in_place(result, |_| Rewrite::Drop);
        assert!(result.is_empty());
        assert_eq!(result.as_ptr(), pointer);
        assert_eq!(result.capacity(), capacity);
        assert!(rewrite_in_place(Vec::new(), |_| unreachable!()).is_empty());
    }

    #[test]
    fn shared_inputs_distinguish_abi_slots_from_scratch_and_duplicates() {
        let mut quantum = Op::empty();
        quantum.kind = OperationType::AppendToRegister;
        quantum.q_target = QubitId(2);
        quantum.r_target = RegisterId(0);
        let mut classical = Op::empty();
        classical.kind = OperationType::AppendToRegister;
        classical.c_target = BitId(11);
        classical.r_target = RegisterId(1);
        let mut scratch = Op::empty();
        scratch.kind = OperationType::X;
        scratch.q_target = QubitId(7);
        let mut scratch_bit = Op::empty();
        scratch_bit.kind = OperationType::BitStore1;
        scratch_bit.c_target = BitId(13);
        let inputs = Inputs::new(&[quantum, classical, quantum, scratch, scratch_bit]);
        assert_eq!(inputs.qubits.len(), 8);
        assert_eq!(inputs.bits.len(), 14);
        assert_eq!(inputs.qubits.iter().filter(|&&input| input).count(), 1);
        assert_eq!(inputs.bits.iter().filter(|&&input| input).count(), 1);
        assert!(inputs.qubits[2] && inputs.bits[11]);
        let state = Support::new(&inputs);
        assert_eq!(state.next_atom, 2);
        assert_eq!(state.qubits[2].atoms, [0]);
        assert_eq!(state.bits[11].atoms, [1]);
        assert!(state.qubits[7].is_zero() && state.bits[13].is_zero());
    }
}
