//! Current physical-slot witnesses for an exact control product.
//!
//! This index observes the same original-op truth state as the older proofs.
//! It makes no Rust allocator-lifetime claim and never creates a value atom.

use super::{Inputs, Rewrite, Support, Truth};
use crate::circuit::{Op, OperationType, QubitId};
use std::collections::{BTreeSet, HashMap};

/// An unsupported query is absent, rather than a fresh opaque expression.
fn exact_product(a: &Truth, b: &Truth) -> Option<Truth> {
    if a.is_zero() || b.is_zero() || a.complements(b) {
        return Some(Truth::constant(false));
    }
    if a.is_one() {
        return Some(b.clone());
    }
    if b.is_one() || a == b {
        return Some(a.clone());
    }
    a.binary(b, true)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Hit {
    witness: QubitId,
    complement: bool,
    zero_product: bool,
}

impl Hit {
    pub(super) fn rewrite(self) -> Rewrite {
        // Zero normalization is reached ONLY after a distinct witness was found.
        if self.zero_product {
            Rewrite::Drop
        } else if self.complement {
            Rewrite::ComplementedCx(self.witness)
        } else {
            Rewrite::Cx(self.witness)
        }
    }
}

pub(super) struct Index {
    values: HashMap<Truth, BTreeSet<usize>>,
    eligible: Vec<bool>,
}

impl Index {
    pub(super) fn new(state: &Support, inputs: &Inputs) -> Self {
        assert_eq!(state.qubits.len(), inputs.qubits.len());
        let mut index = Self {
            values: HashMap::new(),
            eligible: inputs.qubits.clone(),
        };
        for q in 0..index.eligible.len() {
            index.insert(state, q);
        }
        index
    }

    fn insert(&mut self, state: &Support, q: usize) {
        if self.eligible[q] {
            self.values
                .entry(state.qubits[q].clone())
                .or_default()
                .insert(q);
        }
    }

    fn remove(&mut self, state: &Support, q: usize) {
        let value = &state.qubits[q];
        if let Some(slots) = self.values.get_mut(value) {
            slots.remove(&q);
            if slots.is_empty() {
                self.values.remove(value);
            }
        }
    }

    fn permitted(&self, q: usize, op: &Op) -> bool {
        self.eligible[q]
            && q != op.q_control1.0 as usize
            && q != op.q_control2.0 as usize
            && q != op.q_target.0 as usize
    }

    fn lookup(&self, product: &Truth, op: &Op) -> Option<Hit> {
        // Deterministic selection: exact before complement, then smallest slot.
        let find = |value: &Truth| {
            self.values
                .get(value)?
                .iter()
                .copied()
                .find(|&q| self.permitted(q, op))
        };
        let (q, complement) = find(product)
            .map(|q| (q, false))
            .or_else(|| find(&product.complement()).map(|q| (q, true)))?;
        Some(Hit {
            witness: QubitId(q as u64),
            complement,
            zero_product: product.is_zero(),
        })
    }

    pub(super) fn before(&mut self, state: &Support, op: &Op, query_product: bool) -> Option<Hit> {
        for q in quantum_touches(op) {
            if !self.eligible[q] {
                self.eligible[q] = true;
                self.insert(state, q);
            }
        }
        let hit = if query_product && op.kind == OperationType::CCX {
            exact_product(
                &state.qubits[op.q_control1.0 as usize],
                &state.qubits[op.q_control2.0 as usize],
            )
            .and_then(|product| self.lookup(&product, op))
        } else {
            None
        };
        for q in quantum_changes(op) {
            self.remove(state, q);
        }
        hit
    }

    pub(super) fn after(&mut self, state: &Support, op: &Op) {
        // Conservative R43 eligibility: reset slots return only on a later touch.
        if op.kind == OperationType::R {
            self.eligible[op.q_target.0 as usize] = false;
        }
        for q in quantum_changes(op) {
            self.insert(state, q);
        }
    }
}

fn quantum_changes(op: &Op) -> impl Iterator<Item = usize> {
    use OperationType::*;
    let qubits = match op.kind {
        X | CX | CCX | R | Hmr => [Some(op.q_target), None],
        Swap => [Some(op.q_control1), Some(op.q_target)],
        _ => [None; 2],
    };
    qubits.into_iter().flatten().map(|q| q.0 as usize)
}

fn quantum_touches(op: &Op) -> impl Iterator<Item = usize> {
    use OperationType::*;
    let qubits = match op.kind {
        X | Z | R | Hmr => [Some(op.q_target), None, None],
        CX | CZ | Swap => [Some(op.q_control1), Some(op.q_target), None],
        CCX | CCZ => [Some(op.q_control1), Some(op.q_control2), Some(op.q_target)],
        _ => [None; 3],
    };
    qubits.into_iter().flatten().map(|q| q.0 as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::BitId;

    fn atom(id: u64) -> Truth {
        Truth::canonical(vec![id], 2)
    }

    fn initialized(values: Vec<Truth>) -> (Support, Index) {
        let mut state = Support::new(&Inputs::new(&[]));
        state.next_atom = values
            .iter()
            .flat_map(|value| &value.atoms)
            .max()
            .map_or(0, |id| id + 1);
        state.qubits = values;
        state.bits = vec![Truth::constant(false)];
        let mut index = Index {
            values: HashMap::new(),
            eligible: vec![true; state.qubits.len()],
        };
        for q in 0..state.qubits.len() {
            index.insert(&state, q);
        }
        (state, index)
    }

    fn ccx(a: u64, b: u64, target: u64) -> Op {
        let mut op = Op::empty();
        op.kind = OperationType::CCX;
        op.q_control1 = QubitId(a);
        op.q_control2 = QubitId(b);
        op.q_target = QubitId(target);
        op
    }

    fn unary(kind: OperationType, target: u64) -> Op {
        let mut op = Op::empty();
        op.kind = kind;
        op.q_target = QubitId(target);
        op
    }

    #[test]
    fn quantum_slot_iterators_cover_every_operation_kind_in_order() {
        use OperationType::*;
        let cases: [(OperationType, &[usize], &[usize]); 18] = [
            (Neg, &[], &[]),
            (Register, &[], &[]),
            (AppendToRegister, &[], &[]),
            (BitInvert, &[], &[]),
            (BitStore0, &[], &[]),
            (BitStore1, &[], &[]),
            (X, &[13], &[13]),
            (Z, &[13], &[]),
            (CX, &[5, 13], &[13]),
            (CZ, &[5, 13], &[]),
            (Swap, &[5, 13], &[5, 13]),
            (R, &[13], &[13]),
            (Hmr, &[13], &[13]),
            (CCX, &[5, 8, 13], &[13]),
            (CCZ, &[5, 8, 13], &[]),
            (PushCondition, &[], &[]),
            (PopCondition, &[], &[]),
            (DebugPrint, &[], &[]),
        ];
        for (kind, touches, changes) in cases {
            let mut op = ccx(5, 8, 13);
            op.kind = kind;
            assert_eq!(
                quantum_touches(&op).collect::<Vec<_>>(),
                touches,
                "{kind:?}"
            );
            assert_eq!(
                quantum_changes(&op).collect::<Vec<_>>(),
                changes,
                "{kind:?}"
            );
        }
    }

    #[test]
    fn lookup_prefers_exact_then_smallest_permitted_slot() {
        let product = exact_product(&atom(0), &atom(1)).unwrap();
        let (state, mut index) = initialized(vec![
            product.clone(),
            product.clone(),
            product.clone(),
            product.complement(),
            product.clone(),
            product.clone(),
        ]);
        let op = ccx(0, 1, 2);
        assert_eq!(index.lookup(&product, &op).unwrap().witness, QubitId(4));
        index.eligible[4] = false;
        assert_eq!(index.lookup(&product, &op).unwrap().witness, QubitId(5));
        index.remove(&state, 5);
        assert_eq!(
            index.lookup(&product, &op),
            Some(Hit {
                witness: QubitId(3),
                complement: true,
                zero_product: false,
            })
        );
    }

    #[test]
    fn skipping_queries_preserves_index_updates() {
        let values = vec![
            atom(0),
            atom(1),
            Truth::constant(false),
            Truth::constant(false),
        ];
        let (mut state, mut queried) = initialized(values.clone());
        let (_, mut skipped) = initialized(values);
        let mut swap = unary(OperationType::Swap, 3);
        swap.q_control1 = QubitId(2);
        let mut measure = unary(OperationType::Hmr, 2);
        measure.c_target = BitId(0);
        let ops = [
            ccx(0, 1, 2),
            ccx(0, 1, 3),
            unary(OperationType::X, 2),
            swap,
            measure,
            unary(OperationType::R, 3),
            unary(OperationType::Z, 3),
            ccx(0, 1, 2),
        ];
        let mut hits = 0;
        for op in ops {
            op.validate();
            hits += usize::from(queried.before(&state, &op, true).is_some());
            assert_eq!(skipped.before(&state, &op, false), None);
            assert_eq!(queried.values, skipped.values);
            assert_eq!(queried.eligible, skipped.eligible);
            state.step(&op);
            queried.after(&state, &op);
            skipped.after(&state, &op);
            assert_eq!(queried.values, skipped.values);
            assert_eq!(queried.eligible, skipped.eligible);
        }
        assert!(hits > 0);
    }

    #[test]
    fn reset_witness_returns_only_after_a_later_touch() {
        let product = exact_product(&atom(0), &atom(1)).unwrap();
        let (mut state, mut index) =
            initialized(vec![atom(0), atom(1), product.clone(), product.clone()]);
        let query = ccx(0, 1, 3);
        assert_eq!(index.lookup(&product, &query).unwrap().witness, QubitId(2));
        let reset = unary(OperationType::R, 2);
        index.before(&state, &reset, false);
        state.step(&reset);
        index.after(&state, &reset);
        assert!(!index.eligible[2]);
        assert_eq!(index.lookup(&product, &query), None);
        assert_eq!(index.lookup(&Truth::constant(false), &query), None);
        let touch = unary(OperationType::Z, 2);
        index.before(&state, &touch, false);
        state.step(&touch);
        index.after(&state, &touch);
        assert!(index.eligible[2]);
        assert_eq!(
            index.lookup(&Truth::constant(false), &query),
            Some(Hit {
                witness: QubitId(2),
                complement: false,
                zero_product: true,
            })
        );
    }

    #[test]
    fn unsupported_products_never_produce_a_witness() {
        let wide = Truth::canonical((0..6).collect(), 1);
        let (state, mut index) = initialized(vec![wide, atom(6), Truth::constant(false), atom(7)]);
        assert_eq!(index.before(&state, &ccx(0, 1, 2), true), None);
    }

    #[test]
    fn witness_rewrites_preserve_classical_conditions() {
        let mut original = ccx(0, 1, 2);
        original.c_condition = BitId(0);
        for complement in [false, true] {
            let mut output = Vec::new();
            Hit {
                witness: QubitId(3),
                complement,
                zero_product: false,
            }
            .rewrite()
            .emit(original, &mut output);
            assert_eq!(output.len(), if complement { 2 } else { 1 });
            for op in &output {
                op.validate();
                assert_eq!(op.q_target, original.q_target);
                assert_eq!(op.c_condition, original.c_condition);
            }
            if complement {
                assert_eq!(output[0].kind, OperationType::X);
            }
            let last = output.last().unwrap();
            assert_eq!(last.kind, OperationType::CX);
            assert_eq!(last.q_control1, QubitId(3));
        }
    }
}
