//! Exact bounded GF(2) synthesis over CURRENT physical truth functions.
//! A basis witness is an XOR of distinct holder values and an optional constant.
//! No query creates atoms, and holders are never modified by emitted gates.

use super::{product, Support, Truth, SUPPORT_CAP};
use crate::circuit::{Op, OperationType as K, QubitId, NO_QUBIT};
use std::collections::HashSet;

#[derive(Debug)]
pub(super) struct Span {
    constant: bool,
    holders: Vec<usize>,
    phase_factor: Option<usize>,
}

fn expanded(value: &Truth, atoms: &[u64]) -> u64 {
    let positions = value.atoms.iter().map(|a| atoms.binary_search(a).unwrap()).collect::<Vec<_>>();
    let mut table = 0;
    for row in 0..1usize << atoms.len() {
        table |= value.value_in_union(&positions, row) << row;
    }
    table
}

/// Full row-vector elimination; witness bits name independent basis sources.
/// Constant is source zero. Rank is <=64, so a u64 witness is sufficient.
fn synthesize(state: &Support, index: &product::Index, desired: &Truth, excluded: Option<usize>) -> Option<Span> {
    if desired.atoms.len() > SUPPORT_CAP { return None; }
    if desired.is_zero() || desired.is_one() {
        return Some(Span { constant: desired.is_one(), holders: vec![], phase_factor: None });
    }
    if let Some((q, complement)) = index.span_witness(desired, excluded) {
        return Some(Span { constant: complement, holders: vec![q], phase_factor: None });
    }
    let mut basis = [(0u64, 0u64); 64];
    let mut sources = Vec::new();
    let mut insert = |mut vector: u64, source: Option<usize>| {
        let mut witness = 1u64 << sources.len();
        while vector != 0 {
            let pivot = vector.ilog2() as usize;
            let (old, old_witness) = basis[pivot];
            if old == 0 {
                basis[pivot] = (vector, witness);
                sources.push(source);
                return sources.len() == (1usize << desired.atoms.len());
            }
            vector ^= old;
            witness ^= old_witness;
        }
        false
    };
    insert(Truth::row_mask(desired.atoms.len()), None);
    let mut seen = HashSet::new();
    for q in index.span_slots(&desired.atoms, excluded) {
        if !seen.insert(&state.qubits[q]) { continue; }
        let full = insert(expanded(&state.qubits[q], &desired.atoms), Some(q));
        // Dimension equals the number of truth assignments. Never shift by 64.
        if full { break; }
    }
    let mut vector = desired.table;
    let mut witness = 0;
    while vector != 0 {
        let pivot = vector.ilog2() as usize;
        let (old, old_witness) = basis[pivot];
        if old == 0 { return None; }
        vector ^= old;
        witness ^= old_witness;
    }
    let mut holders = Vec::new();
    let mut constant = false;
    for (bit, source) in sources.iter().enumerate() {
        if witness & (1u64 << bit) != 0 {
            match source { None => constant = true, Some(q) => holders.push(*q) }
        }
    }
    Some(Span { constant, holders, phase_factor: None })
}

impl Span {
    fn gate(original: Op, kind: K, control: Option<usize>, target: Option<usize>, result: &mut Vec<Op>) {
        let mut emitted = original;
        emitted.kind = kind;
        emitted.q_control2 = NO_QUBIT;
        emitted.q_control1 = control.map(|q| QubitId(q as u64)).unwrap_or(NO_QUBIT);
        emitted.q_target = target.map(|q| QubitId(q as u64)).unwrap_or(NO_QUBIT);
        emitted.validate();
        result.push(emitted);
    }

    pub(super) fn emit(self, original: Op, result: &mut Vec<Op>) {
        if original.kind == K::CCX {
            let target = original.q_target.0 as usize;
            if self.constant { Self::gate(original, K::X, None, Some(target), result); }
            for q in self.holders {
                assert_ne!(q, target);
                Self::gate(original, K::CX, Some(q), Some(target), result);
            }
        } else {
            assert_eq!(original.kind, K::CCZ);
            if let Some(factor) = self.phase_factor {
                if self.constant { Self::gate(original, K::Z, None, Some(factor), result); }
                for q in self.holders {
                    if q == factor { Self::gate(original, K::Z, None, Some(q), result); }
                    else { Self::gate(original, K::CZ, Some(q), Some(factor), result); }
                }
            } else {
                if self.constant { Self::gate(original, K::Neg, None, None, result); }
                for q in self.holders { Self::gate(original, K::Z, None, Some(q), result); }
            }
        }
    }
}

pub(super) fn before(state: &Support, index: &product::Index, op: &Op) -> Option<Span> {
    if !matches!(op.kind, K::CCX | K::CCZ) { return None; }
    let a = &state.qubits[op.q_control1.0 as usize];
    let b = &state.qubits[op.q_control2.0 as usize];
    // Explicitly bound the ORIGINAL control union, before product cancellation.
    let mut atoms = a.atoms.clone(); atoms.extend(&b.atoms); atoms.sort_unstable(); atoms.dedup();
    if atoms.len() > SUPPORT_CAP { return None; }
    let mut desired = product::exact_product(a, b)?;
    if op.kind == K::CCZ {
        // ab = c XOR XOR(holders) implies abw = cw XOR XOR(holder*w).
        // This remains exact even if w has support outside the six-atom pair.
        if let Some(mut span) = synthesize(state, index, &desired, None) {
            span.phase_factor = Some(op.q_target.0 as usize);
            return Some(span);
        }
        atoms.extend(&state.qubits[op.q_target.0 as usize].atoms); atoms.sort_unstable(); atoms.dedup();
        if atoms.len() > SUPPORT_CAP { return None; }
        desired = product::exact_product(&desired, &state.qubits[op.q_target.0 as usize])?;
    }
    synthesize(state, index, &desired, (op.kind == K::CCX).then_some(op.q_target.0 as usize))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::RegisterId;

    #[test]
    fn span_rank_64_and_target_exclusion() {
        let mut ops = vec![];
        let mut register = Op::empty(); register.kind = K::Register; register.r_target = RegisterId(0); ops.push(register);
        for q in 0..64 {
            let mut append = Op::empty(); append.kind = K::AppendToRegister; append.r_target = RegisterId(0); append.q_target = QubitId(q); ops.push(append);
        }
        let mut state = Support::new(&ops);
        // Every monomial over six immutable variables is an independent vector.
        for subset in 0..64 {
            let mut table = 0;
            for row in 0..64 { if row & subset == subset { table |= 1u64 << row; } }
            state.qubits[subset] = Truth::canonical((0..6).collect(), table);
        }
        let index = product::Index::new(&state, &ops);
        let desired = Truth::canonical((0..6).collect(), 0x9193_5555_5555_5539);
        assert_eq!(desired.atoms.len(), 6);
        let span = synthesize(&state, &index, &desired, None).unwrap();
        let mut table = if span.constant { u64::MAX } else { 0 };
        for q in span.holders { table ^= expanded(&state.qubits[q], &desired.atoms); }
        assert_eq!(table, desired.table);
        // Degree-six monomial cannot be derived without its unique holder.
        assert!(synthesize(&state, &index, &state.qubits[63], Some(63)).is_none());
    }
}
