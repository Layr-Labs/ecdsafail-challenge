use super::Builder;
use crate::circuit::{QubitId, NO_BIT};

/// `u < v` as a phase, applied inside whatever classical condition is already
/// pushed. The caller owns the condition.
///
/// The ladder runs on `~u`, so its carry-out is the carry of `~u + v`, which
/// overflows exactly when `v > u`. `carries[i]` takes the borrow out of bit `i`
/// and `u[i]` is left holding the running prefix; the inverse pass measures each
/// carry out and repairs its phase, so unwinding is free. The top bit never
/// needs a wire at all: its carry step `MAJ(u_top, v_top, carry)` is wanted only
/// as a phase, and `(-1)^(x^y) = (-1)^x (-1)^y` splits that MAJ into three CZs.
///
/// `borrow_in` is the borrow entering bit 0, for a caller that has already
/// accounted for the bits below by other means. With `None` the comparison
/// starts clean, and after the first CX `u[0]` already holds what a clean
/// carry-in wire would have held — so it serves as the first nonlinear control
/// and no wire is needed either way.
pub(crate) fn cmp_lt_phase(
    circ: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    borrow_in: Option<QubitId>,
) {
    cmp_lt_phase_with_scratch(circ, u, v, borrow_in, None);
}

fn cmp_lt_phase_with_scratch(
    circ: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    borrow_in: Option<QubitId>,
    clean_scratch: Option<QubitId>,
) {
    let n = u.len();
    assert_eq!(v.len(), n);
    // Two bits is the narrowest comparison any caller asks for: the walk's
    // boundary repair is the only one that supplies a borrow, and
    // `walk_low_chunk` only splits when `low >= 4`, which leaves it `low - 2`
    // bits wide.
    assert!(n > 1);
    // A source-bit predictor may now lie inside a widened comparison window.
    // If it is the first source bit, MAJ(!u0,v0,v0)=v0: that whole position
    // is redundant. Otherwise restore the predictor before its operand bit
    // is read, and recreate the first control only for the final phase erase.
    // No separate predictor copy or extra nonlinear gate is necessary.
    if borrow_in == Some(v[0]) {
        assert!(
            n >= 3,
            "aliased low seed needs at least two remaining comparison bits"
        );
        return cmp_lt_phase_with_scratch(circ, &u[1..], &v[1..], borrow_in, clean_scratch);
    }
    let operand_seed = borrow_in.is_some_and(|q| v[1..].contains(&q));
    assert!(
        !borrow_in.is_some_and(|q| u.contains(&q)),
        "seed cannot alias the accumulator"
    );
    let last = n - 1;
    let room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    if last > room {
        cmp_lt_phase_low_workspace(circ, u, v, borrow_in, clean_scratch);
        return;
    }

    let carries = circ.alloc_qubits(last);
    circ.x_all(u);

    // Forward: borrow-prefix ladder over bits 0..last.
    circ.cx(u[0], v[0]);
    let first_ctrl = borrow_in.map_or(u[0], |p| {
        circ.cx(u[0], p);
        p
    });
    circ.ccx(first_ctrl, v[0], carries[0]);
    if operand_seed {
        circ.cx(u[0], borrow_in.unwrap());
    }
    circ.cx(carries[0], u[0]);
    for i in 1..last {
        circ.cx(u[i], v[i]);
        circ.cx(u[i], u[i - 1]);
        circ.ccx(u[i - 1], v[i], carries[i]);
        circ.cx(carries[i], u[i]);
    }

    // The top bit's carry step, as three Clifford CZs.
    circ.cz(u[last], v[last]);
    circ.cz(u[last], u[last - 1]);
    circ.cz(v[last], u[last - 1]);

    // Inverse: every carry measured out and phase-repaired, zero Toffoli.
    for i in (1..last).rev() {
        circ.cx(carries[i], u[i]);
        let m = circ.alloc_bit();
        circ.hmr(carries[i], m);
        circ.cz_if(u[i - 1], v[i], m);
        circ.free_bit(m);
        circ.cx(u[i], u[i - 1]);
        circ.cx(u[i], v[i]);
    }
    circ.cx(carries[0], u[0]);
    let m0 = circ.alloc_bit();
    circ.hmr(carries[0], m0);
    match borrow_in {
        Some(p) => {
            if operand_seed {
                circ.cx(u[0], p);
            }
            circ.cz_if(p, v[0], m0);
            circ.cx(u[0], p);
        }
        None => circ.cz_if(u[0], v[0], m0),
    }
    circ.free_bit(m0);
    circ.cx(u[0], v[0]);

    circ.free_vec(&carries);
    circ.x_all(u);
}

// Carry propagation in the complemented accumulator replaces the stored
// ladder. A forward MAJ chain, phase on its carry, and exact inverse preserve
// both operands and the incoming borrow with at most one clean workspace wire.
fn cmp_lt_phase_low_workspace(
    circ: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    borrow_in: Option<QubitId>,
    clean_scratch: Option<QubitId>,
) {
    let operand_seed = borrow_in.is_some_and(|q| v.contains(&q));
    let needs_scratch = borrow_in.is_none() || operand_seed;
    let owned = needs_scratch && clean_scratch.is_none();
    let seed = if needs_scratch {
        let seed = clean_scratch.unwrap_or_else(|| circ.alloc_qubit());
        assert!(!u.contains(&seed) && !v.contains(&seed));
        if let Some(borrow) = borrow_in {
            circ.cx(borrow, seed);
        }
        seed
    } else {
        borrow_in.unwrap()
    };
    circ.x_all(u);
    for i in 0..u.len() {
        let previous = if i == 0 { seed } else { u[i - 1] };
        circ.cx(u[i], v[i]);
        circ.cx(u[i], previous);
        circ.ccx(previous, v[i], u[i]);
    }
    circ.z_if(u[u.len() - 1], NO_BIT);
    for i in (0..u.len()).rev() {
        let previous = if i == 0 { seed } else { u[i - 1] };
        circ.ccx(previous, v[i], u[i]);
        circ.cx(u[i], previous);
        circ.cx(u[i], v[i]);
    }
    circ.x_all(u);
    if operand_seed {
        circ.cx(borrow_in.unwrap(), seed);
    }
    if owned {
        circ.free(seed);
    }
}

/// Measured-erasure repair, the pattern behind every truncated comparison in
/// the circuit.
///
/// `target` is a carry or overflow wire that is cheaper to measure out than to
/// unwind. `hmr` measures it in a basis that costs a known phase, and the
/// comparison below -- run conditionally on the measurement outcome -- applies
/// the cancelling phase by re-deriving `a < b` from the operands.
///
/// **The slices are the window.** Comparing only the top `k` bits of each
/// operand is the sole approximation: the predicate is wrong exactly when both
/// agree across all `k`, i.e. with probability ~2^-k. Widening by one bit costs
/// one Toffoli and halves that error. Callers slice, as they do for every fold
/// window in the tree, and `borrow_in` lets one account for the bits below by
/// other means instead.
///
/// The caller owns `target` and frees it.
#[cfg_attr(test, track_caller)]
pub fn erase_with_compare(
    circ: &mut Builder,
    target: QubitId,
    a: &[QubitId],
    b: &[QubitId],
    borrow_in: Option<QubitId>,
) {
    #[cfg(test)]
    let _measurement = super::measurement::replay::compare(
        a.len(),
        borrow_in.is_some(),
        std::panic::Location::caller().file(),
    );
    let bit = circ.alloc_bit();
    circ.hmr(target, bit);
    circ.push_condition(bit);
    cmp_lt_phase_with_scratch(circ, a, b, borrow_in, Some(target));
    circ.pop_condition();
    circ.free_bit(bit);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn low_workspace_comparison_preserves_operands_and_seed_exhaustively() {
        for width in 2..=6 {
            // None, independent borrow, and every possible source-bit alias.
            for seed_position in 0..width + 2 {
                for lent_scratch in [false, true] {
                    let mut circ = Builder::new();
                    let u = circ.alloc_qubits(width);
                    let v = circ.alloc_qubits(width);
                    let external = circ.alloc_qubit();
                    let scratch = lent_scratch.then(|| circ.alloc_qubit());
                    let borrow = match seed_position {
                        0 => None,
                        1 => Some(external),
                        position => Some(v[position - 2]),
                    };
                    let base = circ.active_qubits();
                    cmp_lt_phase_low_workspace(&mut circ, &u, &v, borrow, scratch);
                    assert_eq!(circ.active_qubits(), base);
                    let ops = circ.take_ops();
                    let (qubits, bits, _, _) = analyze_ops(ops.iter());
                    assert!(qubits <= (2 * width + 2) as u64);
                    let mask = (1usize << width) - 1;
                    let assignments = 1usize << (2 * width + 1);
                    for start in (0..assignments).step_by(64) {
                        let mut rng = Shake256::default().finalize_xof();
                        let mut sim = Simulator::new(
                            (qubits as usize).max(2 * width + 2),
                            bits as usize,
                            &mut rng,
                        );
                        let mut expected_phase = 0;
                        for lane in 0..64.min(assignments - start) {
                            let assignment = start + lane;
                            let a = assignment & mask;
                            let b = (assignment >> width) & mask;
                            let external_value = (assignment >> (2 * width)) & 1;
                            for bit in 0..width {
                                sim.qubits[u[bit].0 as usize] |= (((a >> bit) & 1) as u64) << lane;
                                sim.qubits[v[bit].0 as usize] |= (((b >> bit) & 1) as u64) << lane;
                            }
                            sim.qubits[external.0 as usize] |= (external_value as u64) << lane;
                            let incoming = match seed_position {
                                0 => 0,
                                1 => external_value,
                                position => (b >> (position - 2)) & 1,
                            };
                            expected_phase |= (u64::from(a < b + incoming)) << lane;
                        }
                        let original = sim.qubits.clone();
                        sim.apply_iter(ops.iter());
                        assert_eq!(sim.qubits, original, "width={width}, seed={seed_position}");
                        assert_eq!(
                            sim.phase, expected_phase,
                            "width={width}, seed={seed_position}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn erased_target_supplies_workspace_when_the_budget_is_full() {
        let mut circ = Builder::new();
        let u = circ.alloc_qubits(4);
        let v = circ.alloc_qubits(4);
        let target = circ.alloc_qubit();
        let cap = super::super::pingpong::walk_max_qubits();
        let padding = circ.alloc_qubits(cap - circ.active_qubits() as usize);
        erase_with_compare(&mut circ, target, &u, &v, None);
        assert_eq!(circ.active_qubits() as usize, cap);
        let ops = circ.take_ops();
        assert_eq!(analyze_ops(ops.iter()).0, 9);
        assert_eq!(padding.len(), cap - 9);
        for start in (0..256).step_by(64) {
            let mut rng = Shake256::default().finalize_xof();
            let (_, bits, _, _) = analyze_ops(ops.iter());
            let mut sim = Simulator::new(9, bits as usize, &mut rng);
            for lane in 0..64 {
                let a = (start + lane) & 15;
                let b = (start + lane) >> 4;
                for bit in 0..4 {
                    sim.qubits[u[bit].0 as usize] |= (((a >> bit) & 1) as u64) << lane;
                    sim.qubits[v[bit].0 as usize] |= (((b >> bit) & 1) as u64) << lane;
                }
                sim.qubits[target.0 as usize] |= u64::from(a < b) << lane;
            }
            let mut expected = sim.qubits.clone();
            expected[target.0 as usize] = 0;
            sim.apply_iter(ops.iter());
            assert_eq!(sim.qubits, expected);
            assert_eq!(sim.phase, 0);
        }
    }
}
