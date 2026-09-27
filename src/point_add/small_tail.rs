//! Exact tape-free continuation on a small signed odd integer pair.
//! Negating either input flips every replay selector, but only its own final
//! sign. Magnitude bits therefore determine all remaining nonlinear work.

use super::{const_arith::multi_controlled_x_dirty, Builder};
use crate::circuit::QubitId;
use std::sync::OnceLock;

pub(super) const MAX_WIDTH: usize = 8;

struct Tables {
    signs: Vec<Polynomial>,
    terminal: [Polynomial; 2],
}

struct Polynomial {
    terms: Vec<u16>,
    polarity: u16,
}

fn term_cost(term: usize) -> (usize, usize) {
    // Conservative dirty-workspace costs guide polarity selection. Emission
    // can use spare clean workspace to share products more cheaply.
    match term.count_ones() as usize {
        0 | 1 => (0, 1),
        2 => (1, 0),
        degree => (4 * degree - 8, 0),
    }
}

fn emit_terms(
    circ: &mut Builder,
    variables: &[QubitId],
    terms: &[u16],
    prefix: Option<QubitId>,
    first: usize,
    target: QubitId,
    dirty: &[QubitId],
) {
    if terms.contains(&0) {
        if let Some(prefix) = prefix {
            circ.cx(prefix, target);
        } else {
            circ.x(target);
        }
    }
    for bit in first..variables.len() {
        let children = terms
            .iter()
            .copied()
            .filter(|&term| term != 0 && term.trailing_zeros() as usize == bit)
            .map(|term| term ^ (1 << bit))
            .collect::<Vec<_>>();
        if children.is_empty() {
            continue;
        }
        let Some(prefix) = prefix else {
            emit_terms(
                circ,
                variables,
                &children,
                Some(variables[bit]),
                bit + 1,
                target,
                dirty,
            );
            continue;
        };
        if children == [0] {
            circ.ccx(prefix, variables[bit], target);
        } else if (circ.active_qubits() as usize) < super::pingpong::walk_max_qubits() {
            let product = circ.alloc_qubit();
            circ.ccx(prefix, variables[bit], product);
            emit_terms(
                circ,
                variables,
                &children,
                Some(product),
                bit + 1,
                target,
                dirty,
            );
            // The shared product's inputs are still live and unchanged.
            let measured = circ.alloc_bit();
            circ.hmr(product, measured);
            circ.cz_if(prefix, variables[bit], measured);
            circ.free_bit(measured);
            circ.release_clean(product);
        } else {
            for term in children {
                let mut controls = vec![prefix, variables[bit]];
                controls.extend(
                    variables
                        .iter()
                        .enumerate()
                        .filter_map(|(index, &q)| (term & (1 << index) != 0).then_some(q)),
                );
                multi_controlled_x_dirty(circ, &controls, target, dirty);
            }
        }
    }
}

fn emit_polynomial(
    circ: &mut Builder,
    variables: &[QubitId],
    polynomial: &Polynomial,
    target: QubitId,
    dirty: &[QubitId],
) {
    for (bit, &q) in variables.iter().enumerate() {
        if polynomial.polarity & (1 << bit) != 0 {
            circ.x(q);
        }
    }
    emit_terms(circ, variables, &polynomial.terms, None, 0, target, dirty);
    for (bit, &q) in variables.iter().enumerate().rev() {
        if polynomial.polarity & (1 << bit) != 0 {
            circ.x(q);
        }
    }
}

fn polynomial(table: &[bool]) -> Polynomial {
    assert!(table.len().is_power_of_two() && table.len() <= 1 << (2 * (MAX_WIDTH - 3)));
    let mut coefficients = table.to_vec();
    for bit in 0..table.len().ilog2() {
        for row in 0..table.len() {
            if row & (1 << bit) != 0 {
                coefficients[row] ^= coefficients[row ^ (1 << bit)];
            }
        }
    }
    let costs: Vec<_> = (0..table.len()).map(term_cost).collect();
    let mut cost = (0usize, 0usize);
    for (term, &present) in coefficients.iter().enumerate() {
        if present {
            cost.0 += costs[term].0;
            cost.1 += costs[term].1;
        }
    }
    let mut best_cost = cost;
    let mut best = coefficients.clone();
    let mut best_polarity = 0usize;
    let mut previous = 0usize;
    for index in 1..table.len() {
        let polarity = index ^ (index >> 1);
        let bit = polarity ^ previous;
        // Translating x_k by one toggles each lower cofactor coefficient by
        // its matching coefficient containing x_k. Gray order changes one bit.
        for term in 0..table.len() {
            if term & bit == 0 && coefficients[term | bit] {
                if coefficients[term] {
                    cost.0 -= costs[term].0;
                    cost.1 -= costs[term].1;
                } else {
                    cost.0 += costs[term].0;
                    cost.1 += costs[term].1;
                }
                coefficients[term] = !coefficients[term];
            }
        }
        let candidate_cost = (cost.0, cost.1 + 2 * polarity.count_ones() as usize);
        if candidate_cost < best_cost {
            best_cost = candidate_cost;
            best.clone_from(&coefficients);
            best_polarity = polarity;
        }
        previous = polarity;
    }
    let terms = best
        .into_iter()
        .enumerate()
        .filter_map(|(term, set)| set.then(|| u16::try_from(term).unwrap()))
        .collect();
    Polynomial {
        terms,
        polarity: u16::try_from(best_polarity).unwrap(),
    }
}

fn step(values: &mut [i32; 2], round: usize) -> bool {
    let target = if round % 2 == 0 { 1 } else { 0 };
    let source = 1 - target;
    let negative = (values[source] ^ values[target]) & 2 != 0;
    values[target] = (values[target]
        + if negative {
            -values[source]
        } else {
            values[source]
        })
        / 2;
    assert!(values[target] & 1 != 0);
    negative
}

fn gcd(mut a: i32, mut b: i32) -> i32 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn build_tables(width: usize, parity: usize) -> Tables {
    let magnitude_bits = width - 3;
    let rows = 1usize << (2 * magnitude_bits);
    let mask = (1usize << magnitude_bits) - 1;
    let pair = |row: usize| {
        [
            2 * (row & mask) as i32 + 1,
            2 * (row >> magnitude_bits) as i32 + 1,
        ]
    };
    let limit = (1i32 << (width - 2)) - 1;
    let mut count = 0;
    for row in 0..rows {
        let mut values = pair(row);
        let mut steps = 0;
        while values[0].abs() != values[1].abs() {
            assert!(steps < 2 * limit as usize, "small walk did not converge");
            step(&mut values, parity + steps);
            assert!(values.iter().all(|value| value.abs() <= limit));
            steps += 1;
        }
        count = count.max(steps);
    }
    let mut signs = vec![vec![false; rows]; count];
    let mut terminal = [vec![false; rows], vec![false; rows]];
    for row in 0..rows {
        let mut values = pair(row);
        let common = gcd(values[0], values[1]);
        for (round, table) in signs.iter_mut().enumerate() {
            table[row] = step(&mut values, parity + round);
        }
        assert_eq!((values[0].abs(), values[1].abs()), (common, common));
        for index in 0..2 {
            terminal[index][row] = values[index] < 0;
        }
    }
    Tables {
        signs: signs.iter().map(|table| polynomial(table)).collect(),
        terminal: terminal.map(|table| polynomial(&table)),
    }
}

fn tables(width: usize, first_round: usize) -> &'static Tables {
    assert!((5..=MAX_WIDTH).contains(&width));
    static TABLES: OnceLock<[[Tables; 2]; MAX_WIDTH - 4]> = OnceLock::new();
    &TABLES.get_or_init(|| {
        std::array::from_fn(|index| std::array::from_fn(|parity| build_tables(index + 5, parity)))
    })[width - 5][first_round % 2]
}

pub(super) fn rounds(width: usize, first_round: usize) -> usize {
    tables(width, first_round).signs.len()
}

pub(super) struct SmallTail {
    magnitudes: Vec<QubitId>,
    signs: [QubitId; 2],
    tables: &'static Tables,
}

impl SmallTail {
    /// Two preceding, same-width ordinary rounds prove each top bit is a
    /// duplicate of the next bit. The caller checks that structural precondition.
    pub(super) fn new(
        circ: &mut Builder,
        u: &mut Vec<QubitId>,
        v: &mut Vec<QubitId>,
        first_round: usize,
    ) -> Self {
        let width = u.len();
        assert_eq!(v.len(), width);
        let tables = tables(width, first_round);
        let mut magnitudes = Vec::new();
        for reg in [&mut *u, &mut *v] {
            let top = reg.pop().unwrap();
            let sign = reg[width - 2];
            circ.cx(sign, top);
            circ.release_clean(top);
            for &q in &reg[1..width - 2] {
                circ.cx(sign, q);
                magnitudes.push(q);
            }
        }
        Self {
            magnitudes,
            signs: [u[width - 2], v[width - 2]],
            tables,
        }
    }

    pub(super) fn rounds(&self) -> usize {
        self.tables.signs.len()
    }

    fn toggle(
        &self,
        circ: &mut Builder,
        target: QubitId,
        polynomial: &Polynomial,
        dirty: &[QubitId],
    ) {
        let needed = self.magnitudes.len() - 2;
        assert!(dirty.len() >= needed);
        assert!(dirty[..needed]
            .iter()
            .all(|q| !self.magnitudes.contains(q) && !self.signs.contains(q)));
        emit_polynomial(circ, &self.magnitudes, polynomial, target, dirty);
    }

    pub(super) fn with_sign(
        &self,
        circ: &mut Builder,
        round: usize,
        dirty: &[QubitId],
        body: impl FnOnce(&mut Builder, QubitId),
    ) {
        let terms = &self.tables.signs[round];
        circ.cx(self.signs[1], self.signs[0]);
        self.toggle(circ, self.signs[0], terms, dirty);
        body(circ, self.signs[0]);
        self.toggle(circ, self.signs[0], terms, dirty);
        circ.cx(self.signs[1], self.signs[0]);
    }

    pub(super) fn with_terminal_signs(
        &self,
        circ: &mut Builder,
        dirty: &[QubitId],
        body: impl FnOnce(&mut Builder),
    ) {
        for index in 0..2 {
            self.toggle(circ, self.signs[index], &self.tables.terminal[index], dirty);
        }
        body(circ);
        for index in (0..2).rev() {
            self.toggle(circ, self.signs[index], &self.tables.terminal[index], dirty);
        }
    }

    pub(super) fn restore(self, circ: &mut Builder) {
        let bits = self.magnitudes.len() / 2;
        for index in 0..2 {
            for &q in &self.magnitudes[index * bits..(index + 1) * bits] {
                circ.cx(self.signs[index], q);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn shared_products_reduce_toffolis_without_exceeding_workspace() {
        for (room, expected_toffoli) in [(0, 9), (1, 3), (2, 3)] {
            let mut circ = Builder::new();
            let variables = circ.alloc_qubits(4);
            let target = circ.alloc_qubit();
            let dirty = circ.alloc_qubits(2);
            circ.alloc_qubits(
                super::super::pingpong::walk_max_qubits() - circ.active_qubits() as usize - room,
            );
            let base = circ.active_qubits();
            let polynomial = Polynomial {
                terms: vec![3, 7, 11],
                polarity: 0,
            };
            emit_polynomial(&mut circ, &variables, &polynomial, target, &dirty);
            assert_eq!(circ.active_qubits(), base);
            let ops = circ.take_ops();
            assert_eq!(
                ops.iter()
                    .filter(|op| op.kind == crate::circuit::OperationType::CCX)
                    .count(),
                expected_toffoli
            );
            assert!(analyze_ops(ops.iter()).0 <= super::super::pingpong::walk_max_qubits() as u64);
        }
    }

    #[test]
    fn factored_emission_preserves_all_three_variable_functions_and_phases() {
        for variable_count in 0usize..=3 {
            let rows = 1usize << variable_count;
            for function in 0usize..1usize << rows {
                let truth = (0..rows)
                    .map(|row| function & (1 << row) != 0)
                    .collect::<Vec<_>>();
                let polynomial = polynomial(&truth);
                for room in 0..=variable_count.saturating_sub(2) {
                    let mut circ = Builder::new();
                    let variables = circ.alloc_qubits(variable_count);
                    let target = circ.alloc_qubit();
                    let dirty = circ.alloc_qubits(variable_count.saturating_sub(2));
                    let inputs = circ.active_qubits() as usize;
                    circ.alloc_qubits(super::super::pingpong::walk_max_qubits() - inputs - room);
                    let base = circ.active_qubits();
                    emit_polynomial(&mut circ, &variables, &polynomial, target, &dirty);
                    assert_eq!(circ.active_qubits(), base);
                    let ops = circ.take_ops();
                    let (nq, nb, _, _) = analyze_ops(ops.iter());
                    assert!(nq <= super::super::pingpong::walk_max_qubits() as u64);
                    let mut rng = Shake256::default().finalize_xof();
                    let mut sim = Simulator::new((nq as usize).max(inputs), nb as usize, &mut rng);
                    let assignments = 1usize << inputs;
                    let mut toggle = 0u64;
                    for lane in 0..assignments {
                        for bit in 0..inputs {
                            sim.qubits[bit] |= (((lane >> bit) & 1) as u64) << lane;
                        }
                        toggle |= u64::from(truth[lane & (rows - 1)]) << lane;
                    }
                    let mut expected = sim.qubits.clone();
                    expected[target.0 as usize] ^= toggle;
                    sim.apply_iter(ops.iter());
                    let mask = u64::MAX >> (64 - assignments);
                    for value in &mut sim.qubits {
                        *value &= mask;
                    }
                    assert_eq!(
                        sim.qubits, expected,
                        "variables={variable_count}, function={function}, room={room}"
                    );
                    assert_eq!(sim.phase & mask, 0);
                }
            }
        }
    }

    #[test]
    fn polarity_search_preserves_every_three_variable_function() {
        for variables in 0..=3 {
            let rows = 1usize << variables;
            for function in 0usize..1usize << rows {
                let truth: Vec<_> = (0..rows).map(|row| function & (1 << row) != 0).collect();
                let polynomial = polynomial(&truth);
                for (row, &expected) in truth.iter().enumerate() {
                    let shifted = row ^ usize::from(polynomial.polarity);
                    let actual = polynomial.terms.iter().fold(false, |value, &term| {
                        value ^ (shifted & usize::from(term) == usize::from(term))
                    });
                    assert_eq!(actual, expected);
                }
            }
        }
    }

    #[test]
    fn polarity_search_reduces_a_complemented_product_to_one_term() {
        let mut truth = vec![false; 1024];
        truth[0] = true;
        let polynomial = polynomial(&truth);
        assert_eq!(polynomial.polarity, 1023);
        assert_eq!(polynomial.terms, [1023]);
        assert_eq!(term_cost(1023).0, 32);
    }

    #[test]
    fn all_small_states_have_exact_selectors_and_terminal_signs() {
        for width in 5..=MAX_WIDTH {
            for parity in 0..2 {
                let count = rounds(width, parity);
                assert_eq!(count, [6, 10, 12, 17][width - 5]);
                let mut circ = Builder::new();
                let mut u = circ.alloc_qubits(width);
                let mut v = circ.alloc_qubits(width);
                let original = [u.clone(), v.clone()];
                let dirty = circ.alloc_qubits(2 * (width - 3) - 2);
                let reports = circ.alloc_qubits(count + 2);
                let base = circ.active_qubits();
                let tail = SmallTail::new(&mut circ, &mut u, &mut v, parity);
                assert_eq!(circ.active_qubits(), base - 2);
                for round in 0..count {
                    tail.with_sign(&mut circ, round, &dirty, |circ, sign| {
                        circ.cx(sign, reports[round]);
                        circ.cx(sign, dirty[round % dirty.len()]);
                    });
                    assert_eq!(circ.active_qubits(), base - 2);
                }
                tail.with_terminal_signs(&mut circ, &dirty, |circ| {
                    circ.cx(u[width - 2], reports[count]);
                    circ.cx(v[width - 2], reports[count + 1]);
                    circ.cx(u[width - 2], dirty[0]);
                    circ.cx(v[width - 2], dirty[1]);
                });
                tail.restore(&mut circ);
                for reg in &original {
                    circ.reacquire(reg[width - 1]);
                    circ.cx(reg[width - 2], reg[width - 1]);
                }
                assert_eq!(circ.active_qubits(), base);
                let ops = circ.take_ops();
                let (nq, nb, _, _) = analyze_ops(ops.iter());
                assert!(nq <= base as u64 + dirty.len() as u64 - 2);
                let bits = width - 2;
                let modulus = 1usize << bits;
                let mask = modulus - 1;
                let cases = 1usize << (2 * bits + dirty.len());
                for start in (0..cases).step_by(64) {
                    let mut rng = Shake256::default().finalize_xof();
                    let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
                    let mut expected_reports = vec![0u64; count + 2];
                    let mut dirty_changes = vec![0u64; dirty.len()];
                    for lane in 0..64 {
                        let row = start + lane;
                        let encoded = [row & mask, (row >> bits) & mask];
                        let mut values = encoded.map(|word| {
                            let signed = if word < modulus / 2 {
                                word as i32
                            } else {
                                word as i32 - modulus as i32
                            };
                            2 * signed + 1
                        });
                        let common = gcd(values[0], values[1]);
                        for (reg, value) in original.iter().zip(values) {
                            for (bit, &q) in reg.iter().enumerate() {
                                sim.qubits[q.0 as usize] |= (((value >> bit) & 1) as u64) << lane;
                            }
                        }
                        for (bit, &q) in dirty.iter().enumerate() {
                            sim.qubits[q.0 as usize] |=
                                (((row >> (2 * bits + bit)) & 1) as u64) << lane;
                        }
                        for (round, report) in expected_reports[..count].iter_mut().enumerate() {
                            let sign = u64::from(step(&mut values, parity + round)) << lane;
                            *report |= sign;
                            dirty_changes[round % dirty.len()] ^= sign;
                        }
                        assert_eq!((values[0].abs(), values[1].abs()), (common, common));
                        for index in 0..2 {
                            let sign = u64::from(values[index] < 0) << lane;
                            expected_reports[count + index] |= sign;
                            dirty_changes[index] ^= sign;
                        }
                    }
                    let mut expected = sim.qubits.clone();
                    for (&q, value) in reports.iter().zip(expected_reports) {
                        expected[q.0 as usize] = value;
                    }
                    // Replay may change the dirty field bits between oracle calls.
                    for (&q, change) in dirty.iter().zip(dirty_changes) {
                        expected[q.0 as usize] ^= change;
                    }
                    sim.apply_iter(ops.iter());
                    assert_eq!(
                        sim.qubits, expected,
                        "width={width}, first-round parity={parity}"
                    );
                    assert_eq!(sim.phase, 0);
                }
            }
        }
    }
}
