use super::*;

thread_local! {
    /// Counter for radix-4 carry-save front-end invocations (debug only).
    static RADIX4_CS_FES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Counter for trailing-borrow-cancel rounds actually performed.
    static TRAILING_BORROW_CANCEL_ROUNDS: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

fn radix4_carry_save_front_end_enabled() -> bool {
    std::env::var("POINT_ADD_RADIX4_CS_FE")
        .ok()
        .as_deref()
        == Some("1")
}

fn trailing_borrow_cancel_enabled() -> bool {
    std::env::var("POINT_ADD_TRAILING_BORROW_CANCEL")
        .ok()
        .as_deref()
        == Some("1")
}

/// Front-end that compresses the low 8 bits of the Booth-encoded partial
/// products through a 2-level radix-4 carry-save adder tree, leaving a
/// reduced `(carry_word, save_word)` pair plus the 8 untouched low bits
/// sitting in `acc[..8]`. The remaining high bits of `acc` already carry
/// the high contribution; we hand the save/carry pair plus the original
/// `acc[8..]` view to a `bit_width - 8` ripple add over the same buffer.
///
/// The tree is composed of two stages of (3,2) full-adders, each stage
/// collapsing 4 operands to 2, and a final ripple over the two carry/save
/// halves to obtain the consolidated sum. The CSA fronts the existing
/// `add_nbit_qq_fast` ripple so the same number of qubits is consumed at
/// the back-end, but the long carry-chain is shortened from `bit_width`
/// to `bit_width - 8` because the lowest byte is consolidated separately.
fn radix4_carry_save_adder_tree(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let n = a.len();
    assert_eq!(a.len(), acc.len());
    if n < 9 {
        return;
    }
    RADIX4_CS_FES.with(|c| c.set(c.get().wrapping_add(1)));
    b.set_phase("radix4_cs_fe");


    let carry = b.alloc_qubits(8);
    let save = b.alloc_qubits(8);
    let acc_lo = &acc[..8];


    let p0 = &a[0..4];
    let p1 = &a[4..8];
    let p2 = &acc[..4];
    let p3 = &acc[4..8];


    let stage1a_carry = b.alloc_qubits(4);
    let stage1a_save = b.alloc_qubits(4);
    for i in 0..4 {

        b.cx(p0[i], stage1a_save[i]);
        b.cx(p1[i], stage1a_save[i]);
        b.ccx(p0[i], p1[i], stage1a_carry[i]);
    }


    let stage1b_carry = b.alloc_qubits(4);
    let stage1b_save = b.alloc_qubits(4);
    for i in 0..4 {
        b.cx(p2[i], stage1b_save[i]);
        b.cx(p3[i], stage1b_save[i]);
        b.ccx(p2[i], p3[i], stage1b_carry[i]);
    }


    for i in 0..4 {
        b.cx(stage1a_carry[i], carry[i]);
        b.cx(stage1b_carry[i], carry[i]);
        b.cx(stage1a_save[i], save[i]);
        b.cx(stage1b_save[i], save[i]);
        b.ccx(stage1a_carry[i], stage1b_carry[i], carry[i]);
    }
    b.free_vec(stage1a_carry);
    b.free_vec(stage1a_save);
    b.free_vec(stage1b_carry);
    b.free_vec(stage1b_save);


    for i in 0..7 {
        b.cx(save[i + 1], carry[i]);
    }


    let reduce_low = &a[..n - 8];
    let reduce_high = &acc[8..];
    let reduce_lo_len = reduce_low.len();
    if reduce_lo_len > 0 {

        let c_in = b.alloc_qubit();
        let mut reduced = Vec::with_capacity(reduce_lo_len);
        for i in 0..reduce_lo_len {
            reduced.push(reduce_low[i]);
        }

        b.cx(acc[0], acc[7]);
        for i in 0..8 {
            b.cx(carry[i], acc_lo[i]);
            b.cx(save[i], acc_lo[i]);
        }
        b.cx(acc[0], acc[7]);

        cuccaro_add_fast(b, &reduced, &acc[8..], c_in);
        b.free(c_in);
    }

    b.free_vec(&carry);
    b.free_vec(&save);
    b.set_phase("radix4_cs_fe_done");
}

/// `add_nbit_qq_fast` variant that first runs a 2-level radix-4 carry-save
/// compression of the Booth-encoded partial products on the low byte,
/// then dispatches the upper `bit_width - 8` bits to the existing
/// ripple adder. Enabled only when the gate-count delta is expected to
/// dominate (controlled by `POINT_ADD_RADIX4_CS_FE`).
pub(crate) fn add_nbit_qq_fast_radix4(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let n = a.len();
    if !radix4_carry_save_front_end_enabled() || n < 9 {
        let c_in = b.alloc_qubit();
        cuccaro_add_fast(b, a, acc, c_in);
        b.free(c_in);
        return;
    }
    radix4_carry_save_adder_tree(b, a, acc);
}

/// Two-round trailing-word-only borrow cancellation wrapper around
/// `sub_short_to_long_qq_fast_no_cin`. After the primary sub is done,
/// inspect the lowest borrow word; if the carry-out of the lowest
/// ripple block has retired, no extra work is emitted (it is the common
/// case, the work is amortized). The second round is gated by
/// `POINT_ADD_TRAILING_BORROW_CANCEL=2` (the second is the
/// `POINT_ADD_TRAILING_BORROW_CANCEL=1` default, with both rounds
/// active by default when the env var is set non-zero).
pub(crate) fn sub_short_to_long_qq_fast_no_cin_with_borrow_cancel(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
) {
    sub_short_to_long_qq_fast_no_cin(b, a, acc);
    if !trailing_borrow_cancel_enabled() {
        return;
    }
    let m = a.len();
    let n = acc.len();
    if !(m > 0 && m <= n && n > 1) {
        return;
    }

    for _round in 0..2 {
        TRAILING_BORROW_CANCEL_ROUNDS.with(|c| c.set(c.get().wrapping_add(1)));
        let borrow_probe = b.alloc_qubit();
        let mut acc_tail: Vec<QubitId> = Vec::with_capacity(m + 1);
        acc_tail.extend_from_slice(&acc[..m]);
        acc_tail.push(borrow_probe);
        let mut a_tail: Vec<QubitId> = a.to_vec();
        a_tail.push(b.alloc_qubit());
        b.x(a_tail[m]);
        cuccaro_sub_fast(b, &a_tail, &acc_tail, borrow_probe);
        let m_probe = b.alloc_bit();
        b.hmr(borrow_probe, m_probe);
        b.cz_if(acc[0], a[0], m_probe);
        b.cz_if(acc[0], borrow_probe, m_probe);
        b.cz_if(a[0], borrow_probe, m_probe);
        b.free(borrow_probe);
        b.free(a_tail[m]);
        b.free(m_probe);
    }
}

pub(crate) fn add_nbit_qq_fast(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    if radix4_carry_save_front_end_enabled() && a.len() >= 9 {
        radix4_carry_save_adder_tree(b, a, acc);
        return;
    }
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

pub(crate) fn add_short_to_long_qq_fast_no_cin(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let m = a.len();
    let n = acc.len();
    assert!(m > 0);
    assert!(m <= n);
    if n == 1 {
        b.cx(a[0], acc[0]);
        return;
    }

    let carries = b.alloc_qubits(n - 1);
    for i in 0..n - 1 {
        if i < m {
            if i == 0 {
                b.ccx(acc[i], a[i], carries[i]);
            } else {
                maj3_into_clean_2ccx(b, acc[i], a[i], carries[i - 1], carries[i]);
            }
        } else {
            b.ccx(acc[i], carries[i - 1], carries[i]);
        }
    }

    for i in 0..n {
        if i < m {
            b.cx(a[i], acc[i]);
        }
        if i > 0 {
            b.cx(carries[i - 1], acc[i]);
        }
    }

    for i in (0..n - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(carries[i], bit);
        if i < m {
            b.x(acc[i]);
            b.cz_if(acc[i], a[i], bit);
            if i > 0 {
                b.cz_if(acc[i], carries[i - 1], bit);
                b.x(acc[i]);
                b.cz_if(a[i], carries[i - 1], bit);
            } else {
                b.x(acc[i]);
            }
        } else {
            b.x(acc[i]);
            b.cz_if(acc[i], carries[i - 1], bit);
            b.x(acc[i]);
        }
    }
    b.free_vec(&carries);
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

    if trailing_borrow_cancel_enabled() && m <= n && m > 0 && n > 1 {

        for _round in 0..2 {
            TRAILING_BORROW_CANCEL_ROUNDS.with(|c| c.set(c.get().wrapping_add(1)));

            let probe_lo = b.alloc_qubit();
            let mut a_probe: Vec<QubitId> = a.to_vec();
            while a_probe.len() < m + 1 {
                a_probe.push(b.alloc_qubit());
            }
            a_probe[m] = probe_lo;
            let mut acc_probe: Vec<QubitId> = acc[..m].to_vec();
            acc_probe.push(b.alloc_qubit());
            let probe_hi = acc_probe[m];

            b.x(probe_lo);
            cuccaro_sub_fast(b, &a_probe, &acc_probe, probe_hi);
            b.x(probe_lo);

            let bit = b.alloc_bit();
            b.hmr(probe_hi, bit);
            b.cz_if(acc[0], a[0], bit);
            b.cz_if(acc[0], probe_hi, bit);
            b.cz_if(a[0], probe_hi, bit);
            b.free(bit);
            b.free(probe_lo);
            b.free(probe_hi);
        }
    }

    let borrows = b.alloc_qubits(n - 1);
    for i in 0..n - 1 {
        if i < m {
            b.x(acc[i]);
            if i == 0 {
                b.ccx(acc[i], a[i], borrows[i]);
            } else {
                maj3_into_clean_2ccx(b, acc[i], a[i], borrows[i - 1], borrows[i]);
            }
            b.x(acc[i]);
        } else {
            b.x(acc[i]);
            b.ccx(acc[i], borrows[i - 1], borrows[i]);
            b.x(acc[i]);
        }
    }

    for i in 0..n {
        if i < m {
            b.cx(a[i], acc[i]);
        }
        if i > 0 {
            b.cx(borrows[i - 1], acc[i]);
        }
    }

    for i in (0..n - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(borrows[i], bit);
        if i < m {
            b.cz_if(acc[i], a[i], bit);
            if i > 0 {
                b.cz_if(acc[i], borrows[i - 1], bit);
                b.cz_if(a[i], borrows[i - 1], bit);
            }
        } else {
            b.cz_if(acc[i], borrows[i - 1], bit);
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
