use super::*;

pub(crate) fn add_nbit_qq_fast(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add_fast(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq_fast(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub_fast(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn add_nbit_qq_fast_borrowed_carries(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
    carries: &[QubitId],
) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add_fast_borrowed_carries(b, a, acc, c_in, carries);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq_fast_borrowed_carries(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
    carries: &[QubitId],
) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub_fast_borrowed_carries(b, a, acc, c_in, carries);
    b.free(c_in);
}

#[inline]
fn maj3_into_clean_2ccx(b: &mut B, x: QubitId, y: QubitId, z: QubitId, target: QubitId) {
    debug_assert!(x != y && x != z && x != target && y != z && y != target && z != target);
    b.ccx(x, z, target);
    b.cx(x, z);
    b.ccx(y, z, target);
    b.cx(x, z);
}

/// 2-bit windowed borrow/copy carry lookahead applied to one window
/// (positions `i` and `i + 1` of `acc`) with a given incoming borrow `b_in`.
///
/// `P[i] = a[i] XOR acc[i]` and `G[i] = a[i] AND acc[i]` (or the sub variant
/// with complemented `acc[i]`) are emitted **once per window** rather than
/// once per bit, and the two inner borrows for the window are resolved from
/// a single shared borrow wire `b_out` (the second bit's borrow out) and the
/// incoming `b_in`. `a` is preserved exactly, `acc[i]` and `acc[i + 1]` are
/// restored to their input values on exit by the shared `hmr + cz_if`
/// epilogue, and `b_out` is returned clean.
///
/// Compared to the bit-serial ripple this cuts the borrow-qubit cost roughly
/// in half (one wire per two positions) and removes one of the two
/// `maj3_into_clean_2ccx` per position by absorbing the inner
/// `P[i + 1] AND borrows[i]` into the same wire that already holds
/// `borrows[i + 1]`.
#[inline]
fn lookahead_window_step(
    b: &mut B,
    a_i: QubitId,
    a_next: QubitId,
    acc_i: QubitId,
    acc_next: QubitId,
    b_in: Option<QubitId>,
    b_out: QubitId,
    is_sub: bool,
) {
    debug_assert!(a_i != a_next);
    debug_assert!(acc_i != acc_next);
    debug_assert!(a_i != acc_i);
    debug_assert!(a_next != acc_i);
    debug_assert!(a_next != acc_next);
    debug_assert!(b_out != a_i && b_out != a_next && b_out != acc_i && b_out != acc_next);
    if let Some(bi) = b_in {
        debug_assert!(b_out != bi);
        debug_assert!(bi != a_i && bi != a_next && bi != acc_i && bi != acc_next);
    }

    if is_sub {
        b.x(acc_i);
    }
    if let Some(bi) = b_in {
        b.ccx(acc_i, a_i, b_out);
        b.cx(bi, acc_i);
    } else {
        b.ccx(acc_i, a_i, b_out);
    }
    b.cx(a_i, acc_i);
    if is_sub {
        b.x(acc_i);
    }

    if is_sub {
        b.x(acc_next);
    }
    b.ccx(acc_next, a_next, b_out);
    b.cx(a_next, acc_next);
    b.cx(b_out, acc_next);
    if is_sub {
        b.x(acc_next);
    }
}

#[inline]
fn lookahead_window_uncompute(
    b: &mut B,
    a_i: QubitId,
    a_next: QubitId,
    acc_i: QubitId,
    acc_next: QubitId,
    b_in: Option<QubitId>,
    b_out: QubitId,
    is_sub: bool,
) {
    if is_sub {
        b.x(acc_next);
    }
    let m_next = b.alloc_bit();
    b.hmr(b_out, m_next);
    if is_sub {
        b.cz_if(acc_next, a_next, m_next);
    } else {
        b.x(acc_next);
        b.cz_if(acc_next, a_next, m_next);
        b.x(acc_next);
    }
    b.cx(b_out, acc_next);
    b.cx(a_next, acc_next);
    if is_sub {
        b.x(b_out);
    }
    b.cz_if(b_out, a_next, m_next);
    if is_sub {
        b.x(b_out);
    }
    if is_sub {
        b.x(acc_i);
    }
    b.cx(a_i, acc_i);
    if let Some(bi) = b_in {
        b.cx(bi, acc_i);
    }
    b.cz_if(acc_i, a_i, m_next);
    if let Some(bi) = b_in {
        b.cz_if(acc_i, bi, m_next);
    }
    b.cx(b_out, acc_i);
    if is_sub {
        b.x(acc_i);
    }
}

pub(crate) fn add_short_to_long_qq_fast_no_cin(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let m = a.len();
    let n = acc.len();
    assert!(m > 0);
    assert!(m <= n);
    if n == 1 {
        b.cx(a[0], acc[0]);
        return;
    }

    let n_windows = n / 2;
    let has_tail = n % 2 == 1;
    let needed = n_windows + usize::from(has_tail);
    let borrows = b.alloc_qubits(needed);
    let b_in_for = |k: usize| -> Option<QubitId> {
        if k == 0 {
            None
        } else {
            Some(borrows[k - 1])
        }
    };
    let acc_pair = |k: usize| -> (QubitId, QubitId) {
        let i = 2 * k;
        (acc[i], acc[i + 1])
    };
    let a_pair = |k: usize| -> (QubitId, QubitId) {
        if 2 * k + 1 < m {
            (a[2 * k], a[2 * k + 1])
        } else if 2 * k < m {
            (a[2 * k], a[2 * k])
        } else {
            (a[m - 1], a[m - 1])
        }
    };

    for k in 0..n_windows {
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        lookahead_window_step(b, a_i, a_next, acc_i, acc_next, b_in_for(k), borrows[k], false);
    }
    if has_tail {
        let i = 2 * n_windows;
        let tail_b = borrows[n_windows];
        let (acc_i, _) = acc_pair(n_windows);
        let a_i = if i < m { a[i] } else { a[m - 1] };
        if i == 0 {
            b.ccx(acc_i, a_i, tail_b);
        } else {
            b.x(acc_i);
            b.ccx(acc_i, a_i, tail_b);
            b.x(acc_i);
        }
        b.cx(a_i, acc_i);
        b.cx(borrows[n_windows - 1], acc_i);
    }

    if has_tail {
        let i = 2 * n_windows;
        if i < m {
            b.cx(a[i], acc[i]);
        }
        b.cx(borrows[n_windows - 1], acc[i]);
    }
    for k in (0..n_windows).rev() {
        let i = 2 * k + 1;
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        if i < m {
            b.cx(a_next, acc_next);
        }
        b.cx(borrows[k], acc_next);
        if 2 * k < m {
            b.cx(a_i, acc_i);
        }
        b.cx(borrows[k], acc_i);
        if k > 0 {
            b.cx(borrows[k - 1], acc_i);
        }
    }

    for k in (0..n_windows).rev() {
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        lookahead_window_uncompute(b, a_i, a_next, acc_i, acc_next, b_in_for(k), borrows[k], false);
    }
    if has_tail {
        let i = 2 * n_windows;
        let acc_i = acc[i];
        let a_i = if i < m { a[i] } else { a[m - 1] };
        let tail_b = borrows[n_windows];
        let m_tail = b.alloc_bit();
        b.hmr(tail_b, m_tail);
        b.x(acc_i);
        b.cz_if(acc_i, a_i, m_tail);
        b.x(acc_i);
        b.cz_if(tail_b, a_i, m_tail);
        b.cx(tail_b, acc_i);
        if i < m {
            b.cx(a_i, acc_i);
        }
        if n_windows > 0 {
            b.cx(borrows[n_windows - 1], acc_i);
        }
        b.cz_if(acc_i, borrows.get(n_windows.wrapping_sub(1)).copied().unwrap_or(tail_b), m_tail);
    }
    b.free_vec(&borrows);
}

pub(crate) fn sub_short_to_long_qq_fast_no_cin(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let m = a.len();
    let n = acc.len();
    assert!(m > 0);
    assert!(m <= n);
    if n == 1 {
        b.cx(a[0], acc[0]);
        return;
    }

    let n_windows = n / 2;
    let has_tail = n % 2 == 1;
    let needed = n_windows + usize::from(has_tail);
    let borrows = b.alloc_qubits(needed);
    let b_in_for = |k: usize| -> Option<QubitId> {
        if k == 0 {
            None
        } else {
            Some(borrows[k - 1])
        }
    };
    let acc_pair = |k: usize| -> (QubitId, QubitId) {
        let i = 2 * k;
        (acc[i], acc[i + 1])
    };
    let a_pair = |k: usize| -> (QubitId, QubitId) {
        if 2 * k + 1 < m {
            (a[2 * k], a[2 * k + 1])
        } else if 2 * k < m {
            (a[2 * k], a[2 * k])
        } else {
            (a[m - 1], a[m - 1])
        }
    };

    for k in 0..n_windows {
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        lookahead_window_step(b, a_i, a_next, acc_i, acc_next, b_in_for(k), borrows[k], true);
    }
    if has_tail {
        let i = 2 * n_windows;
        let tail_b = borrows[n_windows];
        let acc_i = acc[i];
        let a_i = if i < m { a[i] } else { a[m - 1] };
        if i == 0 {
            b.x(acc_i);
            b.ccx(acc_i, a_i, tail_b);
            b.x(acc_i);
        } else {
            b.x(acc_i);
            b.ccx(acc_i, a_i, tail_b);
            b.x(acc_i);
        }
        b.cx(a_i, acc_i);
        if n_windows > 0 {
            b.cx(borrows[n_windows - 1], acc_i);
        }
    }

    if has_tail {
        let i = 2 * n_windows;
        if i < m {
            b.cx(a[i], acc[i]);
        }
        if n_windows > 0 {
            b.cx(borrows[n_windows - 1], acc[i]);
        }
    }
    for k in (0..n_windows).rev() {
        let i = 2 * k + 1;
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        if i < m {
            b.cx(a_next, acc_next);
        }
        b.cx(borrows[k], acc_next);
        if 2 * k < m {
            b.cx(a_i, acc_i);
        }
        b.cx(borrows[k], acc_i);
        if k > 0 {
            b.cx(borrows[k - 1], acc_i);
        }
    }

    for k in (0..n_windows).rev() {
        let (a_i, a_next) = a_pair(k);
        let (acc_i, acc_next) = acc_pair(k);
        lookahead_window_uncompute(b, a_i, a_next, acc_i, acc_next, b_in_for(k), borrows[k], true);
    }
    if has_tail {
        let i = 2 * n_windows;
        let acc_i = acc[i];
        let a_i = if i < m { a[i] } else { a[m - 1] };
        let tail_b = borrows[n_windows];
        let prev_b = if n_windows > 0 { Some(borrows[n_windows - 1]) } else { None };
        let m_tail = b.alloc_bit();
        b.hmr(tail_b, m_tail);
        b.cz_if(acc_i, a_i, m_tail);
        if let Some(pb) = prev_b {
            b.cz_if(acc_i, pb, m_tail);
            b.cz_if(a_i, pb, m_tail);
        }
        b.cx(tail_b, acc_i);
        if i < m {
            b.cx(a_i, acc_i);
        }
        if let Some(pb) = prev_b {
            b.cx(pb, acc_i);
        }
    }
    b.free_vec(&borrows);
}

pub(crate) fn add_nbit_qq(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn add_nbit_const(b: &mut B, acc: &[QubitId], c: U256) {
    let n = acc.len();
    let a = load_const(b, n, c);
    add_nbit_qq(b, &a, acc);
    unload_const(b, &a, c);
}

pub(crate) fn sub_nbit_const(b: &mut B, acc: &[QubitId], c: U256) {
    let n = acc.len();
    let a = load_const(b, n, c);
    sub_nbit_qq(b, &a, acc);
    unload_const(b, &a, c);
}
