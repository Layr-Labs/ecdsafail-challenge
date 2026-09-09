//! Current physical-slot witnesses for an exact control product.
//!
//! This index observes the same original-op truth state as the older proofs.
//! It makes no Rust allocator-lifetime claim and never creates a value atom.

use super::{Rewrite, Support, Truth, SUPPORT_CAP};
use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit};
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
    let mut table = 0;
    for row in 0..1usize << atoms.len() {
        table |= (a.value_in_union(&left, row) & b.value_in_union(&right, row)) << row;
    }
    Some(Truth::canonical(atoms, table))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Hit {
    witness: QubitId,
    complement: bool,
    zero_product: bool,
}

impl Hit {
    pub(super) fn emit(self, original: Op, result: &mut Vec<Op>) {
        // Zero normalization is reached ONLY after a distinct witness was found.
        if self.zero_product {
            return;
        }
        if self.complement {
            Rewrite::X.emit(original, result);
        }
        Rewrite::Cx(self.witness).emit(original, result);
    }
}

pub(super) struct Index {
    values: HashMap<Truth, BTreeSet<usize>>,
    eligible: Vec<bool>,
}

impl Index {
    pub(super) fn new(state: &Support, ops: &[Op]) -> Self {
        let mut index = Self {
            values: HashMap::new(),
            eligible: vec![false; state.qubits.len()],
        };
        let (_, _, _, registers) = analyze_ops(ops.iter());
        for register in registers {
            for slot in register {
                if let QubitOrBit::Qubit(q) = slot {
                    index.eligible[q.0 as usize] = true;
                }
            }
        }
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
        for (value, complement) in [(product.clone(), false), (product.complement(), true)] {
            if let Some(slots) = self.values.get(&value) {
                if let Some(&q) = slots.iter().find(|&&q| self.permitted(q, op)) {
                    return Some(Hit {
                        witness: QubitId(q as u64),
                        complement,
                        zero_product: product.is_zero(),
                    });
                }
            }
        }
        None
    }

    pub(super) fn before(&mut self, state: &Support, op: &Op) -> Option<Hit> {
        for q in quantum_touches(op) {
            if !self.eligible[q] {
                self.eligible[q] = true;
                self.insert(state, q);
            }
        }
        let hit = if op.kind == OperationType::CCX {
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

fn quantum_changes(op: &Op) -> Vec<usize> {
    use OperationType::*;
    match op.kind {
        X | CX | CCX | R | Hmr => vec![op.q_target.0 as usize],
        Swap => vec![op.q_control1.0 as usize, op.q_target.0 as usize],
        _ => vec![],
    }
}

fn quantum_touches(op: &Op) -> Vec<usize> {
    use OperationType::*;
    match op.kind {
        X | Z | R | Hmr => vec![op.q_target.0 as usize],
        CX | CZ | Swap => vec![op.q_control1.0 as usize, op.q_target.0 as usize],
        CCX | CCZ => vec![
            op.q_control1.0 as usize,
            op.q_control2.0 as usize,
            op.q_target.0 as usize,
        ],
        _ => vec![],
    }
}

#[cfg(test)]
#[path = "product_simplify_tests.rs"]
mod tests;
