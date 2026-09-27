//! Exact Boolean tables over at most six immutable value atoms.
//! Tables retain only essential variables. An unsupported union of supports
//! becomes one fresh atom for the WHOLE result, including any constant term.
//! Atom functions can be correlated; universal Boolean identities remain valid.

use super::affine_simplify::{rewrite_in_place, Inputs, Rewrite, Support as AffineSupport};
use super::quadratic_simplify::Support as QuadraticSupport;
use crate::circuit::{Op, OperationType, NO_BIT};

const SUPPORT_CAP: usize = 6;
const LOW_COFACTORS: [u64; SUPPORT_CAP] = [
    0x5555_5555_5555_5555,
    0x3333_3333_3333_3333,
    0x0f0f_0f0f_0f0f_0f0f,
    0x00ff_00ff_00ff_00ff,
    0x0000_ffff_0000_ffff,
    0x0000_0000_ffff_ffff,
];

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
            let shift = 1usize << position;
            if (table ^ (table >> shift)) & LOW_COFACTORS[position] != 0 {
                position += 1;
                continue;
            }
            // Compact the zero cofactor, closing one gap in every row index.
            table &= LOW_COFACTORS[position];
            for bit in position..SUPPORT_CAP - 1 {
                table = (table | (table >> (1usize << bit))) & LOW_COFACTORS[bit + 1];
            }
            atoms.remove(position);
        }
        Self { atoms, table }
    }

    fn table_in_union(&self, atoms: &[u64]) -> u64 {
        let mut table = self.table;
        let mut own = 0;
        for (position, atom) in atoms.iter().enumerate() {
            if self.atoms.get(own) == Some(atom) {
                own += 1;
                continue;
            }
            // Insert an unused variable: spread row blocks, then duplicate
            // each block into its identical one cofactor.
            for bit in (position..SUPPORT_CAP - 1).rev() {
                table = (table | (table << (1usize << bit))) & LOW_COFACTORS[bit];
            }
            table |= table << (1usize << position);
        }
        debug_assert_eq!(own, self.atoms.len());
        table
    }

    fn binary(&self, other: &Self, is_and: bool) -> Option<Self> {
        let mut union = [0; SUPPORT_CAP];
        let (mut count, mut left, mut right) = (0, 0, 0);
        while left < self.atoms.len() || right < other.atoms.len() {
            if count == SUPPORT_CAP {
                return None;
            }
            union[count] = match (self.atoms.get(left), other.atoms.get(right)) {
                (Some(&a), Some(&b)) if a == b => {
                    left += 1;
                    right += 1;
                    a
                }
                (Some(&a), Some(&b)) if a < b => {
                    left += 1;
                    a
                }
                (Some(&a), None) => {
                    left += 1;
                    a
                }
                (_, Some(&b)) => {
                    right += 1;
                    b
                }
                (None, None) => unreachable!(),
            };
            count += 1;
        }
        let atoms = &union[..count];
        let left = self.table_in_union(atoms);
        let right = other.table_in_union(atoms);
        let table = if is_and { left & right } else { left ^ right };
        Some(Self::canonical(atoms.to_vec(), table))
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
    fn new(inputs: &Inputs) -> Self {
        let mut state = Self {
            qubits: vec![Truth::constant(false); inputs.qubits.len()],
            bits: vec![Truth::constant(false); inputs.bits.len()],
            base_condition: Truth::constant(true),
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

    fn fresh(&mut self) -> Truth {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("truth atom identifier overflow");
        Truth {
            atoms: vec![id],
            table: 2,
        }
    }

    fn combine(&mut self, a: &Truth, b: &Truth, is_and: bool) -> Truth {
        // Unsupported computations still receive distinct whole-value atoms.
        a.binary(b, is_and).unwrap_or_else(|| self.fresh())
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
    let inputs = Inputs::new(&ops);
    let mut affine = AffineSupport::new(&inputs);
    let mut quadratic = QuadraticSupport::new(&inputs);
    let mut truth = Support::new(&inputs);
    let mut products = use_products.then(|| product::Index::new(&truth, &inputs));
    rewrite_in_place(ops, |op| {
        let affine_rewrite = affine.step(op);
        let quadratic_rewrite = quadratic.step(op);
        let query_product =
            matches!(affine_rewrite, Rewrite::Keep) && matches!(quadratic_rewrite, Rewrite::Keep);
        // Query the pre-op state; remove old keys before truth mutates it.
        let product_hit = products
            .as_mut()
            .and_then(|index| index.before(&truth, op, query_product));
        let truth_rewrite = truth.step(op);
        if let Some(index) = &mut products {
            index.after(&truth, op);
        }
        let rewrite = match (affine_rewrite, quadratic_rewrite) {
            (Rewrite::Keep, Rewrite::Keep) => truth_rewrite,
            (Rewrite::Keep, quadratic_proof) => quadratic_proof,
            (affine_proof, _) => affine_proof,
        };
        match (rewrite, product_hit) {
            (Rewrite::Keep, Some(hit)) => hit.rewrite(),
            (old_proof, _) => old_proof,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference_canonical(mut atoms: Vec<u64>, mut table: u64) -> Truth {
        table &= Truth::row_mask(atoms.len());
        let mut position = 0;
        while position < atoms.len() {
            let bit = 1usize << position;
            if (0..1usize << atoms.len())
                .any(|row| row & bit == 0 && ((table >> row) ^ (table >> (row | bit))) & 1 != 0)
            {
                position += 1;
                continue;
            }
            let mut reduced = 0;
            for row in 0..1usize << (atoms.len() - 1) {
                let original = (row & (bit - 1)) | ((row & !(bit - 1)) << 1);
                reduced |= ((table >> original) & 1) << row;
            }
            atoms.remove(position);
            table = reduced;
        }
        Truth { atoms, table }
    }

    fn reference_binary(a: &Truth, b: &Truth, is_and: bool) -> Option<Truth> {
        let mut atoms = a.atoms.clone();
        atoms.extend(&b.atoms);
        atoms.sort_unstable();
        atoms.dedup();
        if atoms.len() > SUPPORT_CAP {
            return None;
        }
        let positions = |value: &Truth| {
            value
                .atoms
                .iter()
                .map(|id| atoms.binary_search(id).unwrap())
                .collect::<Vec<_>>()
        };
        let left = positions(a);
        let right = positions(b);
        let value_at = |value: &Truth, positions: &[usize], row: usize| {
            let mut own_row = 0;
            for (own, &union) in positions.iter().enumerate() {
                own_row |= ((row >> union) & 1) << own;
            }
            (value.table >> own_row) & 1
        };
        let mut table = 0;
        for row in 0..1usize << atoms.len() {
            let a = value_at(a, &left, row);
            let b = value_at(b, &right, row);
            table |= (if is_and { a & b } else { a ^ b }) << row;
        }
        Some(reference_canonical(atoms, table))
    }

    fn next_word(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    fn samples() -> Vec<Truth> {
        let mut state = 0x4a27_6103_d8c9_b5ef;
        (0u32..1 << (SUPPORT_CAP + 1))
            .filter(|mask| mask.count_ones() as usize <= SUPPORT_CAP)
            .map(|mask| {
                let atoms = (0..SUPPORT_CAP + 1)
                    .filter(|bit| mask & (1 << bit) != 0)
                    .map(|bit| 3 + 17 * bit as u64)
                    .collect();
                reference_canonical(atoms, next_word(&mut state))
            })
            .collect()
    }

    #[test]
    fn canonical_matches_every_four_variable_function() {
        for count in 0..=4 {
            let atoms: Vec<_> = (0..count).map(|bit| 3 + 17 * bit as u64).collect();
            for table in 0..=Truth::row_mask(count) {
                assert_eq!(
                    Truth::canonical(atoms.clone(), table),
                    reference_canonical(atoms.clone(), table)
                );
            }
        }
    }

    #[test]
    fn canonical_handles_full_tables_and_nonessential_columns() {
        let mut state = 0x1d0f_39a6_7c82_b5e4;
        for count in 0..=SUPPORT_CAP {
            let atoms: Vec<_> = (0..count).map(|bit| 3 + 17 * bit as u64).collect();
            for _ in 0..2048 {
                let table = next_word(&mut state);
                assert_eq!(
                    Truth::canonical(atoms.clone(), table),
                    reference_canonical(atoms.clone(), table)
                );
                for mask in LOW_COFACTORS {
                    assert_eq!(
                        Truth::canonical(atoms.clone(), mask),
                        reference_canonical(atoms.clone(), mask)
                    );
                }
            }
        }
    }

    #[test]
    fn binary_matches_scalar_reference_for_all_support_pairs() {
        let values = samples();
        for a in &values {
            for b in &values {
                for is_and in [false, true] {
                    assert_eq!(
                        a.binary(b, is_and),
                        reference_binary(a, b, is_and),
                        "a={a:?}, b={b:?}, and={is_and}"
                    );
                }
            }
        }
    }

    #[test]
    fn unsupported_results_remain_distinct_opaque_values() {
        let a = Truth {
            atoms: (0..SUPPORT_CAP as u64).collect(),
            table: 1,
        };
        let b = Truth {
            atoms: vec![SUPPORT_CAP as u64],
            table: 2,
        };
        let mut state = Support::new(&Inputs::new(&[]));
        state.next_atom = SUPPORT_CAP as u64 + 1;
        let first = state.combine(&a, &b, true);
        let second = state.combine(&a, &b, true);
        assert_eq!(first.table, 2);
        assert_eq!(second.table, 2);
        assert_ne!(first.atoms, second.atoms);
        assert!(a.binary(&b, false).is_none());
    }

    #[test]
    fn all_passes_preserve_conditional_products_phase_and_cleanup() {
        use super::super::builder::Builder;
        use crate::circuit::analyze_ops;
        use crate::sim::Simulator;
        use sha3::{
            digest::{ExtendableOutput, Update},
            Shake256,
        };

        let mut circ = Builder::new();
        let q = circ.alloc_qubits(4);
        let bit = circ.alloc_bit();
        circ.ccx(q[0], q[1], q[3]);
        circ.push_condition(bit);
        circ.ccx(q[0], q[1], q[2]);
        circ.pop_condition();
        circ.x(q[3]);
        circ.push_condition(bit);
        circ.ccx(q[0], q[1], q[2]);
        circ.pop_condition();
        circ.x(q[3]);
        circ.ccx(q[0], q[1], q[3]);
        circ.free(q[3]);
        circ.cz(q[0], q[2]);
        circ.declare_qubit_register(&q[..3]);
        circ.declare_bit_register(&[bit]);
        let original = circ.take_ops();
        let (nq, nb, _, _) = analyze_ops(original.iter());
        let simulate = |ops: &[Op]| {
            let mut hash = Shake256::default();
            hash.update(b"simplifier-conditional-products");
            let mut rng = hash.finalize_xof();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
            sim.qubits[..3].copy_from_slice(&[
                0xaaaa_aaaa_aaaa_aaaa,
                0xcccc_cccc_cccc_cccc,
                0xf0f0_f0f0_f0f0_f0f0,
            ]);
            sim.bits[0] = 0xff00_ff00_ff00_ff00;
            sim.apply_iter(ops.iter());
            (sim.qubits, sim.bits, sim.phase)
        };
        let expected = simulate(&original);
        assert_eq!(expected.0[3], 0);
        let passes: [(&str, fn(Vec<Op>) -> Vec<Op>); 4] = [
            ("affine", super::super::affine_simplify::simplify),
            ("quadratic", super::super::quadratic_simplify::simplify),
            ("truth", simplify),
            ("product", simplify_products),
        ];
        for (name, pass) in passes {
            let output = pass(original.clone());
            assert_eq!(simulate(&output), expected, "{name}");
            if name == "product" {
                assert_eq!(output.len(), original.len() + 1);
                assert_eq!(
                    output
                        .iter()
                        .filter(|op| op.kind == OperationType::CCX)
                        .count(),
                    2
                );
            }
        }
    }

    #[test]
    #[ignore = "manual timing comparison against the scalar reference"]
    fn bit_parallel_truth_benchmark() {
        use std::hint::black_box;
        use std::time::Instant;

        let values = samples();
        let measure = |combine: fn(&Truth, &Truth, bool) -> Option<Truth>| {
            let start = Instant::now();
            let mut checksum = 0u64;
            for _ in 0..8 {
                for a in &values {
                    for b in &values {
                        for is_and in [false, true] {
                            if let Some(value) = combine(black_box(a), black_box(b), is_and) {
                                checksum = checksum.wrapping_add(black_box(value.table));
                            }
                        }
                    }
                }
            }
            (start.elapsed(), checksum)
        };
        let (reference, expected) = measure(reference_binary);
        let (parallel, actual) = measure(Truth::binary);
        assert_eq!(expected, actual);
        println!(
            "TRUTH_TABLE_BENCH scalar_seconds={:.6} parallel_seconds={:.6} speedup={:.2}",
            reference.as_secs_f64(),
            parallel.as_secs_f64(),
            reference.as_secs_f64() / parallel.as_secs_f64()
        );
    }
}
