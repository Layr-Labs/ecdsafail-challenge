
use crate::circuit::{analyze_ops, Op, OperationType, QubitOrBit, NO_BIT};

const SUPPORT_CAP: usize = 6;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Truth {
    atoms: Vec<u64>,
    table: u64,
}

impl Truth {
    fn row_mask(count: usize) -> u64 {
        if count >= SUPPORT_CAP {
            u64::MAX
        } else {
            (1u64 << (1usize << count)) - 1
        }
    }
    fn constant(value: bool) -> Self {
        Self { atoms: Vec::new(), table: u64::from(value) }
    }
    fn is_zero(&self) -> bool {
        self.atoms.is_empty() && self.table == 0
    }
    fn is_one(&self) -> bool {
        self.atoms.is_empty() && self.table == 1
    }
    fn canonical(mut atoms: Vec<u64>, mut table: u64) -> Self {
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
        for register in &registers {
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
        self.next_atom = id.checked_add(1).expect("ccx_const atom overflow");
        Truth { atoms: vec![id], table: 2 }
    }

    fn combine(&mut self, a: &Truth, b: &Truth, is_and: bool) -> Truth {
        let mut atoms = a.atoms.clone();
        atoms.extend(&b.atoms);
        atoms.sort_unstable();
        atoms.dedup();
        if atoms.len() > SUPPORT_CAP {
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
        self.combine(a, b, false)
    }

    fn and(&mut self, a: &Truth, b: &Truth) -> Truth {
        if a.is_zero() || b.is_zero() {
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
}

enum Rewrite {
    Keep,
    Drop,
    X,
    Cx(QubitId),
    Z(QubitId),
    Cz(QubitId, QubitId),
    Neg,
}

use crate::circuit::QubitId;


fn emit(rewrite: Rewrite, op: Op, result: &mut Vec<Op>) {
    match rewrite {
        Rewrite::Keep => result.push(op),
        Rewrite::Drop => {}
        rewrite => {
            let mut replacement = Op::empty();
            replacement.c_condition = op.c_condition;
            match rewrite {
                Rewrite::X => {
                    replacement.kind = OperationType::X;
                    replacement.q_target = op.q_target;
                }
                Rewrite::Cx(control) => {
                    replacement.kind = OperationType::CX;
                    replacement.q_control1 = control;
                    replacement.q_target = op.q_target;
                }
                Rewrite::Z(wire) => {
                    replacement.kind = OperationType::Z;
                    replacement.q_target = wire;
                }
                Rewrite::Cz(a, b) => {
                    replacement.kind = OperationType::CZ;
                    replacement.q_control1 = a;
                    replacement.q_target = b;
                }
                Rewrite::Neg => {
                    replacement.kind = OperationType::Neg;
                }
                _ => unreachable!(),
            }
            replacement.validate();
            result.push(replacement);
        }
    }
}

impl Support {
    fn step(&mut self, op: &Op) -> Rewrite {
        if op.kind == OperationType::PushCondition {
            self.condition_stack.push(self.base_condition.clone());
            let bit = self.bits[op.c_condition.0 as usize].clone();
            let base = self.base_condition.clone();
            self.base_condition = self.and(&base, &bit);
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
            let bit = self.bits[op.c_condition.0 as usize].clone();
            condition = self.and(&condition, &bit);
        }

        match op.kind {
            OperationType::CCX => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let b = self.qubits[op.q_control2.0 as usize].clone();
                let product = self.and(&a, &b);
                let fire = self.and(&condition, &product);
                let target = op.q_target.0 as usize;
                let t = self.qubits[target].clone();
                self.qubits[target] = self.xor(&t, &fire);
                if fire.is_zero() {
                    return Rewrite::Drop;
                }
                if fire == condition {
                    return Rewrite::X;
                }
                let ca = self.and(&condition, &a);
                if fire == ca {
                    return Rewrite::Cx(op.q_control1);
                }
                let cb = self.and(&condition, &b);
                if fire == cb {
                    return Rewrite::Cx(op.q_control2);
                }
                Rewrite::Keep
            }
            OperationType::CCZ => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let b = self.qubits[op.q_control2.0 as usize].clone();
                let t = self.qubits[op.q_target.0 as usize].clone();
                let ab = self.and(&a, &b);
                let abt = self.and(&ab, &t);
                let fire = self.and(&condition, &abt);
                if fire.is_zero() {
                    return Rewrite::Drop;
                }
                if fire == condition {
                    return Rewrite::Neg;
                }
                let ab_c = self.and(&condition, &ab);
                if fire == ab_c {
                    return Rewrite::Cz(op.q_control1, op.q_control2);
                }
                let at = self.and(&a, &t);
                let at_c = self.and(&condition, &at);
                if fire == at_c {
                    return Rewrite::Cz(op.q_control1, op.q_target);
                }
                let bt = self.and(&b, &t);
                let bt_c = self.and(&condition, &bt);
                if fire == bt_c {
                    return Rewrite::Cz(op.q_control2, op.q_target);
                }
                let ca = self.and(&condition, &a);
                if fire == ca {
                    return Rewrite::Z(op.q_control1);
                }
                let cb = self.and(&condition, &b);
                if fire == cb {
                    return Rewrite::Z(op.q_control2);
                }
                let ct = self.and(&condition, &t);
                if fire == ct {
                    return Rewrite::Z(op.q_target);
                }
                Rewrite::Keep
            }
            OperationType::CX => {
                let target = op.q_target.0 as usize;
                let c = self.qubits[op.q_control1.0 as usize].clone();
                let toggle = self.and(&condition, &c);
                let t = self.qubits[target].clone();
                self.qubits[target] = self.xor(&t, &toggle);
            }
            OperationType::X => {
                let target = op.q_target.0 as usize;
                let t = self.qubits[target].clone();
                self.qubits[target] = self.xor(&t, &condition);
            }
            OperationType::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                let av = self.qubits[a].clone();
                let bv = self.qubits[b].clone();
                let difference = self.xor(&av, &bv);
                let toggle = self.and(&condition, &difference);
                let left = self.xor(&av, &toggle);
                let right = self.xor(&bv, &toggle);
                self.qubits[a] = left;
                self.qubits[b] = right;
            }
            OperationType::Hmr => {
                let target = op.q_target.0 as usize;
                let bit = op.c_target.0 as usize;
                let outcome = self.fresh();
                let old_bit = self.bits[bit].clone();
                let difference = self.xor(&old_bit, &outcome);
                let toggle = self.and(&condition, &difference);
                self.bits[bit] = self.xor(&old_bit, &toggle);
                let nv = condition.complement();
                let qt = self.qubits[target].clone();
                self.qubits[target] = self.and(&qt, &nv);
            }
            OperationType::R => {
                let target = op.q_target.0 as usize;
                let nv = condition.complement();
                let qt = self.qubits[target].clone();
                self.qubits[target] = self.and(&qt, &nv);
            }
            OperationType::BitInvert => {
                let bit = op.c_target.0 as usize;
                let v = self.bits[bit].clone();
                self.bits[bit] = self.xor(&v, &condition);
            }
            OperationType::BitStore0 => {
                let bit = op.c_target.0 as usize;
                let nv = condition.complement();
                let v = self.bits[bit].clone();
                self.bits[bit] = self.and(&v, &nv);
            }
            OperationType::BitStore1 => {
                let bit = op.c_target.0 as usize;
                let nv = condition.complement();
                let v = self.bits[bit].clone();
                let kept = self.and(&v, &nv);
                self.bits[bit] = self.xor(&kept, &condition);
            }
            OperationType::Z
            | OperationType::CZ
            | OperationType::Neg
            | OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {}
            OperationType::PushCondition | OperationType::PopCondition => unreachable!(),
        }
        Rewrite::Keep
    }
}

impl Truth {
    fn complement(&self) -> Self {
        Self {
            atoms: self.atoms.clone(),
            table: self.table ^ Self::row_mask(self.atoms.len()),
        }
    }
}

pub(crate) fn run(ops: Vec<Op>) -> Vec<Op> {
    let mut state = Support::new(&ops);
    let mut result = Vec::with_capacity(ops.len());
    let mut dropped = 0usize;
    for op in ops {
        let rewrite = state.step(&op);
        if !matches!(rewrite, Rewrite::Keep) {
            dropped += 1;
        }
        emit(rewrite, op, &mut result);
    }
    eprintln!("ccx_const: {} joint-fire Toffolis rewritten", dropped);
    result
}
