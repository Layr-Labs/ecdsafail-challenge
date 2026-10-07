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
/// `borrow_in` is the borrow entering bit 0, for a caller that has already
/// accounted for the bits below by other means. With `None` the comparison
/// starts clean, and after the first CX `u[0]` already holds what a clean
/// carry-in wire would have held — so it serves as the first nonlinear control
/// and no wire is needed either way.
fn cmp_lt_phase(circ: &mut Builder, u: &[QubitId], v: &[QubitId], borrow_in: Option<QubitId>) {
    let n = u.len();
    assert_eq!(v.len(), n);
    // Two bits is the narrowest comparison any caller asks for: the walk's
    // boundary repair is the only one that supplies a borrow, and
    // `walk_low_chunk` only splits when `low >= 4`, which leaves it `low - 2`
    // bits wide.
    assert!(n > 1);
    let last = n - 1;

    let carries = circ.alloc_qubits(last);
    circ.x_all(u);

    // Forward: borrow-prefix ladder over bits 0..last.
    circ.cx(u[0], v[0]);
    let first_ctrl = borrow_in.map_or(u[0], |p| {
        circ.cx(u[0], p);
        p
    });
    circ.ccx(first_ctrl, v[0], carries[0]);
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
