use super::Builder;
use crate::circuit::QubitId;

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
/// If the full measured ladder exceeds the workspace budget, its high stages
/// use in-place majority and inverse-majority instead. Each such stage trades
/// one additional Toffoli for one fewer owned carry, without changing the
/// comparison window or its predicate.
///
/// `borrow_in` is the borrow entering bit 0, for a caller that has already
/// accounted for the bits below by other means. With `None` the comparison
/// starts clean, and after the first CX `u[0]` already holds what a clean
/// carry-in wire would have held — so it serves as the first nonlinear control
/// and no wire is needed either way.
pub(crate) fn cmp_lt_phase(circ: &mut Builder, u: &[QubitId], v: &[QubitId], borrow_in: Option<QubitId>) {
    let room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    cmp_lt_phase_with_scratch(circ, u, v, borrow_in, room);
}

fn cmp_lt_phase_with_scratch(
    circ: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    borrow_in: Option<QubitId>,
    scratch: usize,
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
    if borrow_in==Some(v[0]) {
        assert!(n>=3,"aliased low seed needs at least two remaining comparison bits");
        return cmp_lt_phase_with_scratch(circ,&u[1..],&v[1..],borrow_in,scratch);
    }
    let operand_seed=borrow_in.is_some_and(|q|v[1..].contains(&q));
    assert!(!borrow_in.is_some_and(|q|u.contains(&q)),"seed cannot alias the accumulator");
    let last = n - 1;

    assert!(scratch > 0, "phase comparison requires one scratch qubit");
    let owned = last.min(scratch);
    let carries = circ.alloc_qubits(owned);
    circ.x_all(u);

    // Forward: borrow-prefix ladder over bits 0..last.
    circ.cx(u[0], v[0]);
    let first_ctrl = borrow_in.map_or(u[0], |p| {
        circ.cx(u[0], p);
        p
    });
    circ.ccx(first_ctrl, v[0], carries[0]);
    if operand_seed {circ.cx(u[0],borrow_in.unwrap());}
    circ.cx(carries[0], u[0]);
    for i in 1..last {
        circ.cx(u[i], v[i]);
        circ.cx(u[i], u[i - 1]);
        if i < owned {
            circ.ccx(u[i - 1], v[i], carries[i]);
            circ.cx(carries[i], u[i]);
        } else {
            // An in-place MAJ stores the same borrow prefix in u[i].
            // Its inverse costs one extra Toffoli instead of a scratch wire.
            circ.ccx(u[i - 1], v[i], u[i]);
        }
    }

    // The top bit's carry step, as three Clifford CZs.
    circ.cz(u[last], v[last]);
    circ.cz(u[last], u[last - 1]);
    circ.cz(v[last], u[last - 1]);

    // Unwind owned products by measurement and in-place stages by inverse MAJ.
    for i in (1..last).rev() {
        if i < owned {
            circ.cx(carries[i], u[i]);
            let m = circ.alloc_bit();
            circ.hmr(carries[i], m);
            circ.cz_if(u[i - 1], v[i], m);
            circ.free_bit(m);
        } else {
            circ.ccx(u[i - 1], v[i], u[i]);
        }
        circ.cx(u[i], u[i - 1]);
        circ.cx(u[i], v[i]);
    }
    circ.cx(carries[0], u[0]);
    let m0 = circ.alloc_bit();
    circ.hmr(carries[0], m0);
    match borrow_in {
        Some(p) => {
            if operand_seed {circ.cx(u[0],p);}
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
pub fn erase_with_compare(
    circ: &mut Builder,
    target: QubitId,
    a: &[QubitId],
    b: &[QubitId],
    borrow_in: Option<QubitId>,
) {
    let bit = circ.alloc_bit();
    circ.hmr(target, bit);
    circ.push_condition(bit);
    cmp_lt_phase(circ, a, b, borrow_in);
    circ.pop_condition();
    circ.free_bit(bit);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::OperationType;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn bounded_phase_comparison_exhaustive() {
        for width in 2..=6 {
            for scratch in 1..width {
                for seed in 0..width + 2 {
                    if seed == 2 && width == 2 {
                        continue;
                    }
                    for conditional in [false, true] {
                        let mut circ = Builder::new();
                        let u = circ.alloc_qubits(width);
                        let v = circ.alloc_qubits(width);
                        let external = circ.alloc_qubit();
                        let condition = circ.alloc_bit();
                        let borrow = match seed {
                            0 => None,
                            1 => Some(external),
                            _ => Some(v[seed - 2]),
                        };
                        if conditional {
                            circ.push_condition(condition);
                        }
                        cmp_lt_phase_with_scratch(&mut circ, &u, &v, borrow, scratch);
                        if conditional {
                            circ.pop_condition();
                        }
                        let (nq, nb) = circ.i13_dims();
                        assert!(nq <= 2 * width + 1 + scratch);
                        let ops = circ.take_ops();
                        for op in &ops {
                            op.validate();
                        }
                        let steps = width - 1 - usize::from(seed == 2);
                        assert_eq!(
                            ops.iter().filter(|op| op.kind == OperationType::CCX).count(),
                            2 * steps - steps.min(scratch)
                        );
                        let mut xof = Shake256::default().finalize_xof();
                        let mut sim = Simulator::new(nq, nb, &mut xof);
                        let mask = (1usize << width) - 1;
                        for base in (0..1usize << (2 * width + 1)).step_by(64) {
                            sim.clear_for_shot();
                            sim.bits[condition.0 as usize] = 0xaaaa_aaaa_aaaa_aaaa;
                            let mut expected_phase = 0u64;
                            for shot in 0..64 {
                                let state = base + shot;
                                let a = state & mask;
                                let b = state >> width & mask;
                                let carry = match seed {
                                    0 => false,
                                    1 => state >> (2 * width) & 1 != 0,
                                    _ => b >> (seed - 2) & 1 != 0,
                                };
                                if (!conditional || shot & 1 != 0)
                                    && (a < b || (a == b && carry))
                                {
                                    expected_phase |= 1 << shot;
                                }
                                for (i, &q) in u.iter().chain(&v).chain([&external]).enumerate() {
                                    sim.qubits[q.0 as usize] |= ((state >> i & 1) as u64) << shot;
                                }
                            }
                            sim.apply_iter(ops.iter());
                            assert_eq!(
                                sim.phase, expected_phase,
                                "width={width}, scratch={scratch}, seed={seed}"
                            );
                            assert!(sim.qubits[2 * width + 1..].iter().all(|&q| q == 0));
                            for shot in 0..64 {
                                let state = base + shot;
                                for (i, &q) in u.iter().chain(&v).chain([&external]).enumerate() {
                                    assert_eq!(
                                        sim.qubits[q.0 as usize] >> shot & 1,
                                        (state >> i & 1) as u64
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
