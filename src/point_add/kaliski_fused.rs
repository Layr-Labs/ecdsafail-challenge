//! H1.A1: Kaliski bulk-prefix iterations with fused boundary swaps.
//!
//! The plain bulk iteration `i` does
//!   flags(a_i) · cswap(a_i) · steps 4–8 · cswap(a_i) · a_i ^= ¬s[0]
//! so between iteration i's swap-back and iteration i+1's swap only the flag
//! computation of i+1 runs, and it never writes u, v, r or s. Here the two
//! swaps are fused into one cswap controlled by `a_i ⊕ a_{i+1}`:
//!
//!   iteration i+1, entered with `o = a_i` still live and the registers
//!   still in orientation `o` (i.e. swap^o of the canonical state C_i):
//!     1. step 1 reads u[0], v[0] through a 1-bit cswap(o)           (2 CCX)
//!     2. step 2 compares in orientation o: for physical (U, V),
//!          gt(u_C, v_C) = o ⊕ carry(~V + U + o)
//!        i.e. the same comparator with its carry-in loaded from o     (0 CCX)
//!     3. one cswap controlled by o ⊕ a_{i+1} (a_{i+1} ^= o; swap; a_{i+1} ^= o)
//!        → orientation a_{i+1}, exactly as after the plain step 3
//!     4. uncompute o with the plain step-10 invariant o = ¬s_C[0],
//!        reading s_C[0] through a 1-bit cswap(a_{i+1}) on (r[0], s[0]) (2 CCX)
//!     5. steps 4–8 unchanged; a_{i+1} is handed to the next iteration.
//!   The block is closed by the plain step-9 swap + step 10 of the last
//!   iteration. The backward pass is the exact mirror.
//!
//! Every gate added is CX/CCX/Fredkin; `o` is cleared by XOR with a value it
//! provably equals (the same invariant the plain step 10 uses); the
//! comparator's carry-in qubit is returned to `o` before it is CX-cleared.
//! Widths: the fused swap uses the iteration-(i+1) step-3 widths. The plain
//! step-9 widths of iteration i are equal for (r,s) and one bit wider for
//! (u,v) in late iterations, but that extra bit is zero at the start of
//! iteration i+1 (the invariant the plain step-3 truncation already relies on),
//! so swapping it or not is the same permutation on reachable states.

use super::*;

/// Fused-swap switch (H1.A1/A2). A compile-time constant, not an env var, so
/// the emitted circuit cannot depend on the caller's environment. Set to
/// `false` and rebuild to get the pre-H1 (unfused) Kaliski iterations.
pub(super) const FUSED_SWAP: bool = true;

pub(super) fn fused_enabled() -> bool {
    FUSED_SWAP
}

pub(super) fn uv_width(n: usize, i: usize) -> usize {
    let w = if i < n { n } else { 2 * n - i };
    if H4_FIT_WIDTHS {
        w.min(super::kaliski_widths::U_WIDTH[i] as usize)
    } else {
        w
    }
}

fn rs_width_step3(n: usize, i: usize) -> usize {
    let w = if i + 1 < n { i + 1 } else { n };
    if H4_FIT_WIDTHS {
        w.min(super::kaliski_widths::R_WIDTH[i] as usize)
    } else {
        w
    }
}

/// H4.A7: bitlen(u) + bitlen(v) ≤ 2n − i at the start of iteration i, so the
/// smaller of the two (the one step 4 subtracts, after the swap) fits in
/// ⌊(2n − i)/2⌋ bits.
pub(super) fn min_width(n: usize, i: usize) -> usize {
    let w = uv_width(n, i);
    let w = if H4_MIN_WIDTH_LOAD { w.min((2 * n - i) / 2) } else { w };
    if H4_FIT_WIDTHS {
        w.min(super::kaliski_widths::M_WIDTH[i] as usize)
    } else {
        w
    }
}

/// r/s width after step 9 of iteration i, i.e. at the entry of iteration i+1.
pub(super) fn rs_width_step9(n: usize, i: usize) -> usize {
    let w = if i + 2 < n { i + 2 } else { n };
    if H4_FIT_WIDTHS {
        w.min(super::kaliski_widths::R_WIDTH[i + 1] as usize)
    } else {
        w
    }
}

/// H4.A11: step-4 scratch widths. Forward touches tmp[..uv] (load, subtract)
/// and tmp[..rs3] (r transform, s-add); backward tmp[..rs9] and tmp[..uv].
fn fwd_tmp_width(n: usize, i: usize) -> usize {
    if H4_TIGHT_SCRATCH { uv_width(n, i).max(rs_width_step3(n, i)) } else { n }
}

fn bwd_tmp_width(n: usize, i: usize) -> usize {
    if H4_TIGHT_SCRATCH { uv_width(n, i).max(rs_width_step9(n, i)) } else { n }
}

/// Whether r's doubling (forward) / halving (backward) in iteration i can be a
/// plain shift: true when the doubled r provably fits below 2^n, so the
/// Solinas correction would be the identity.
fn r_plain_shift(n: usize, i: usize) -> bool {
    if H4_FIT_WIDTHS {
        rs_width_step9(n, i) < n
    } else {
        i < r_small_threshold()
    }
}

/// H2.A1 P2 (lazy Kaliski allocation): grow or shrink a register to `len`
/// qubits. Only called at points where the Kaliski invariants guarantee the
/// qubits being freed are |0⟩ (the harness checks every freed qubit) and
/// fresh qubits are |0⟩ by allocation.
/// H4.A16: `lazy_resize` for v when it is the caller's own register `ids`:
/// freed high bits are reserved (only iteration-local allocations may reuse
/// them) and regrowth re-acquires the exact ids.
pub(super) fn lazy_resize_alias(b: &mut B, reg: &mut Vec<QubitId>, len: usize, ids: &[QubitId]) {
    while reg.len() > len {
        let q = reg.pop().expect("nonempty");
        b.free_reserved(q);
    }
    while reg.len() < len {
        let q = b.alloc_specific(ids[reg.len()]);
        reg.push(q);
    }
}

pub(super) fn lazy_resize(b: &mut B, reg: &mut Vec<QubitId>, len: usize) {
    while reg.len() > len {
        let q = reg.pop().expect("nonempty");
        b.free(q);
    }
    while reg.len() < len {
        let q = b.alloc_qubit();
        reg.push(q);
    }
}

/// `with_gt` whose comparison is evaluated in orientation `o`: when `o` is
/// set, (u, v) physically hold (v_C, u_C) and the flag still receives
/// u_C > v_C. With `o = None` this is gate-for-gate the plain `with_gt`.
pub(super) fn with_gt_oriented<F: FnOnce(&mut B)>(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    o: Option<QubitId>,
    flag: QubitId,
    body: F,
) {
    // with_gt(u, v) = with_lt(v, u): carry of (~v + u + c_in).
    let (x, y) = (v, u);
    let n = x.len();
    assert_eq!(n, y.len());
    let c_in = b.alloc_qubit();
    if let Some(o) = o {
        b.cx(o, c_in);
    }
    let carries = b.alloc_qubits(n);
    for i in 0..n {
        b.x(x[i]);
    }

    b.cx(x[0], y[0]);
    b.cx(x[0], c_in);
    b.ccx(c_in, y[0], carries[0]);
    b.cx(carries[0], x[0]);
    for i in 1..n {
        b.cx(x[i], y[i]);
        b.cx(x[i], x[i - 1]);
        b.ccx(x[i - 1], y[i], carries[i]);
        b.cx(carries[i], x[i]);
    }

    b.cx(x[n - 1], flag);
    if let Some(o) = o {
        b.cx(o, flag);
    }
    body(b);
    if let Some(o) = o {
        b.cx(o, flag);
    }
    b.cx(x[n - 1], flag);

    for i in (1..n).rev() {
        b.cx(carries[i], x[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(x[i - 1], y[i], m);
        b.cx(x[i], x[i - 1]);
        b.cx(x[i], y[i]);
    }
    b.cx(carries[0], x[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, y[0], m0);
    b.cx(x[0], c_in);
    b.cx(x[0], y[0]);

    for i in 0..n {
        b.x(x[i]);
    }
    b.free_vec(&carries);
    if let Some(o) = o {
        b.cx(o, c_in);
    }
    b.free(c_in);
}

/// o ^= ¬s_C[0], where the registers are in orientation `a` (s_C[0] sits in
/// r[0] when a = 1). Self-inverse.
fn xor_not_s0_oriented(b: &mut B, a: QubitId, r: &[QubitId], s: &[QubitId], o: QubitId) {
    cswap(b, a, r[0], s[0]);
    b.x(s[0]);
    b.cx(s[0], o);
    b.x(s[0]);
    cswap(b, a, r[0], s[0]);
}

/// Forward bulk iteration with fused swaps. Enters in orientation `a_prev`
/// (canonical if None) and returns `a_f`, leaving the registers in
/// orientation `a_f` (still to be swapped back by the next iteration or by
/// `close_fused_fwd`).
pub(super) fn bulk_iteration_fused_fwd(
    b: &mut B,
    p: U256,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    m_i: QubitId,
    iter_idx: usize,
    a_prev: Option<QubitId>,
) -> QubitId {
    let n = N;
    let a_f = b.alloc_qubit();
    let b_f = b.alloc_qubit();
    let add_f = b.alloc_qubit();
    let f1 = b.alloc_qubit();
    b.x(f1);

    let _kal_saved_phase = b.phase;
    b.set_phase("kal_fused_step1");
    if let Some(o) = a_prev {
        cswap(b, o, u[0], v_w[0]);
    }
    b.x(a_f);
    b.cx(u[0], a_f); // a_f = !u0
    b.x(v_w[0]);
    b.ccx(u[0], v_w[0], m_i); // m_i = u0 & !v0
    b.x(v_w[0]);
    b.cx(a_f, b_f);
    b.cx(m_i, b_f); // b_f = a_f xor m_i
    if let Some(o) = a_prev {
        cswap(b, o, u[0], v_w[0]);
    }

    b.set_phase("kal_fused_step2");
    let cmp_width = uv_width(n, iter_idx);
    let l_gt = b.alloc_qubit();
    with_gt_oriented(b, &u[..cmp_width], &v_w[..cmp_width], a_prev, l_gt, |b| {
        b.x(b_f);
        let t = b.alloc_qubit();
        b.ccx(l_gt, b_f, t);
        b.cx(t, a_f);
        b.cx(t, m_i);
        {
            let tm = b.alloc_bit();
            b.hmr(t, tm);
            b.cz_if(l_gt, b_f, tm);
        }
        b.free(t);
        b.x(b_f);
    });
    b.free(l_gt);

    b.set_phase("kal_fused_step3_cswap");
    // One swap from orientation a_prev to orientation a_f.
    if let Some(o) = a_prev {
        b.cx(o, a_f);
    }
    for j in 0..uv_width(n, iter_idx) {
        cswap(b, a_f, u[j], v_w[j]);
    }
    for j in 0..rs_width_step3(n, iter_idx) {
        cswap(b, a_f, r[j], s[j]);
    }
    if let Some(o) = a_prev {
        b.cx(o, a_f);
        // Previous iteration's step 10, read through the new orientation.
        xor_not_s0_oriented(b, a_f, r, s, o);
        b.free(o);
    }

    b.set_phase("kal_fused_step4");
    b.x(add_f);
    b.cx(b_f, add_f);
    {
        let sub_width = uv_width(n, iter_idx);
        let load_width = min_width(n, iter_idx); // add∧u is 0 above this
        let tmp = b.alloc_qubits(fwd_tmp_width(n, iter_idx));
        for i in 0..load_width {
            b.ccx(add_f, u[i], tmp[i]);
        }
        b.prof("step4:sub_nbit_qq_fast", |b| sub_nbit_qq_fast(b, &tmp[..sub_width], &v_w[..sub_width]));
        let transform_width = rs_width_step3(n, iter_idx);
        // u[i] for i >= u.len() is a lazily-unallocated zero bit, where
        // (u ⊕ r) = r, so load add∧r directly.
        let tw_u = transform_width.min(u.len());
        for i in 0..tw_u {
            b.cx(r[i], u[i]);
        }
        for i in 0..transform_width {
            if i < tw_u {
                b.ccx(add_f, u[i], tmp[i]);
            } else {
                b.ccx(add_f, r[i], tmp[i]);
            }
        }
        for i in 0..tw_u {
            b.cx(r[i], u[i]);
        }
        let add_width = rs_width_step9(n, iter_idx);
        let mut tmp_slice: Vec<QubitId> = tmp[0..transform_width].to_vec();
        // add∧r is 0 above transform_width; with fitted widths the s-add can be
        // several bits wider than the load (rs_width_step9 − rs_width_step3 ≥ 1).
        let tmp_pad = b.alloc_qubits(add_width.saturating_sub(transform_width));
        tmp_slice.extend_from_slice(&tmp_pad);
        let s_slice: Vec<QubitId> = s[0..add_width].to_vec();
        b.prof("step4:add_nbit_qq_fast", |b| add_nbit_qq_fast(b, &tmp_slice, &s_slice));
        b.free_vec(&tmp_pad);
        for i in 0..tmp.len() {
            let m = b.alloc_bit();
            b.hmr(tmp[i], m);
            if i < transform_width {
                b.cz_if(add_f, r[i], m);
            } else if i < load_width {
                b.cz_if(add_f, u[i], m);
            }
        }
        b.free_vec(&tmp);
    }

    b.set_phase("kal_fused_step5");
    b.x(b_f);
    {
        let sm = b.alloc_bit();
        b.hmr(add_f, sm);
        b.cz_if(f1, b_f, sm);
    }
    b.x(b_f);
    b.cx(m_i, b_f);
    b.cx(a_f, b_f);

    b.set_phase("kal_fused_step6_7_8");
    for i in 0..(v_w.len().min(uv_width(n, iter_idx)) - 1) {
        b.swap(v_w[i], v_w[i + 1]);
    }
    if r_plain_shift(n, iter_idx) {
        mod_double_no_corr(b, r);
    } else {
        mod_double_inplace_fast(b, r, p);
    }

    b.x(f1);
    b.free(f1);
    b.free(add_f);
    b.free(b_f);
    b.set_phase(_kal_saved_phase);
    a_f
}

/// Plain step 9 + step 10 of the last fused iteration: back to canonical
/// orientation and clear `a`.
pub(super) fn close_fused_fwd(
    b: &mut B,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    iter_idx: usize,
    a: QubitId,
) {
    let n = N;
    let _kal_saved_phase = b.phase;
    b.set_phase("kal_fused_close");
    for j in 0..uv_width(n, iter_idx) {
        cswap(b, a, u[j], v_w[j]);
    }
    for j in 0..rs_width_step9(n, iter_idx) {
        cswap(b, a, r[j], s[j]);
    }
    b.x(s[0]);
    b.cx(s[0], a);
    b.x(s[0]);
    b.free(a);
    b.set_phase(_kal_saved_phase);
}

/// Inverse of `close_fused_fwd`: recompute `a` and re-enter its orientation.
pub(super) fn open_fused_bwd(
    b: &mut B,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    iter_idx: usize,
) -> QubitId {
    let n = N;
    let _kal_saved_phase = b.phase;
    b.set_phase("bk_fused_open");
    let a = b.alloc_qubit_unreserved(); // carried into the next iteration
    b.x(s[0]);
    b.cx(s[0], a);
    b.x(s[0]);
    for j in (0..rs_width_step9(n, iter_idx)).rev() {
        cswap(b, a, r[j], s[j]);
    }
    for j in (0..uv_width(n, iter_idx)).rev() {
        cswap(b, a, u[j], v_w[j]);
    }
    b.set_phase(_kal_saved_phase);
    a
}

/// Inverse of `bulk_iteration_fused_fwd`. Enters in orientation `a_f` with
/// `a_f` live; leaves in orientation `a_prev` and returns it (None at i = 0,
/// where the registers end canonical).
pub(super) fn bulk_iteration_fused_bwd(
    b: &mut B,
    p: U256,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    m_i: QubitId,
    iter_idx: usize,
    a_f: QubitId,
) -> Option<QubitId> {
    let n = N;
    let b_f = b.alloc_qubit();
    let add_f = b.alloc_qubit();

    let _kal_saved_phase = b.phase;

    // Reverse STEP 8+7 and STEP 6.
    b.set_phase("bk_fused_step6_7_8");
    if r_plain_shift(n, iter_idx) {
        mod_halve_no_corr(b, r);
    } else {
        let mut dirty: Vec<QubitId> = u.to_vec();
        dirty.extend_from_slice(v_w);
        mod_halve_inplace_fast_with_dirty(b, r, p, Some(&dirty));
    }
    for i in (0..(v_w.len().min(uv_width(n, iter_idx)) - 1)).rev() {
        b.swap(v_w[i], v_w[i + 1]);
    }

    // Reverse STEP 5.
    b.set_phase("bk_fused_step5");
    b.cx(a_f, b_f);
    b.cx(m_i, b_f);
    b.x(add_f);
    b.cx(b_f, add_f);

    // Reverse STEP 4.
    b.set_phase("bk_fused_step4");
    {
        let tmp = b.alloc_qubits(bwd_tmp_width(n, iter_idx));
        let load_width = rs_width_step3(n, iter_idx);
        for i in 0..load_width {
            b.ccx(add_f, r[i], tmp[i]);
        }
        let sub_width = rs_width_step9(n, iter_idx);
        b.prof("step4:sub_nbit_qq_fast", |b| sub_nbit_qq_fast(b, &tmp[0..sub_width], &s[0..sub_width]));
        let transform_width = uv_width(n, iter_idx);
        // add∧u is 0 above mw (u is the smaller operand): there tmp only needs
        // its loaded add∧r cleared, and nothing above the loaded bits.
        let mw = min_width(n, iter_idx);
        // r[i] for i >= r.len() is a lazily-unallocated zero bit: CX(r→u) is a no-op.
        let tw_r = mw.min(r.len());
        for i in 0..tw_r {
            b.cx(r[i], u[i]);
        }
        for i in 0..transform_width {
            if i < mw {
                b.ccx(add_f, u[i], tmp[i]);
            } else if i < load_width {
                b.ccx(add_f, r[i], tmp[i]);
            }
        }
        for i in 0..tw_r {
            b.cx(r[i], u[i]);
        }
        b.prof("step4:add_nbit_qq_fast", |b| add_nbit_qq_fast(b, &tmp[0..transform_width], &v_w[0..transform_width]));
        for i in 0..tmp.len() {
            let m = b.alloc_bit();
            b.hmr(tmp[i], m);
            if i < mw {
                b.cz_if(add_f, u[i], m);
            } else if i >= transform_width && i < load_width {
                b.cz_if(add_f, r[i], m);
            }
        }
        b.free_vec(&tmp);
    }
    b.cx(b_f, add_f);
    b.x(add_f);

    // Reverse fused STEP 3: recompute the previous flag, then swap back to
    // orientation a_prev.
    b.set_phase("bk_fused_step3_cswap");
    let a_prev = if iter_idx > 0 {
        let o = b.alloc_qubit_unreserved(); // carried into the next iteration
        xor_not_s0_oriented(b, a_f, r, s, o);
        b.cx(o, a_f);
        Some(o)
    } else {
        None
    };
    for j in (0..rs_width_step3(n, iter_idx)).rev() {
        cswap(b, a_f, r[j], s[j]);
    }
    for j in (0..uv_width(n, iter_idx)).rev() {
        cswap(b, a_f, u[j], v_w[j]);
    }
    if let Some(o) = a_prev {
        b.cx(o, a_f);
    }

    if H4_MEAS_BWD_FLAGS {
        // H4.A1: here the flags are fixed functions of the restored (u,v):
        //   a = 1⊕u0c⊕t, m = u0c⊕u0v0⊕t, b = 1⊕u0v0, t = l·u0·v0,
        // l = [u_C > v_C], u0c = canonical bit 0 = u0 ⊕ o·u0 ⊕ o·v0, and
        // u0·v0 is the same in either orientation. X-measure all three
        // (0 Toffoli) and cancel the kicked phase (−1)^{ca·a + cm·m + cb·b}.
        b.set_phase("bk_fused_meas_flags");
        let ca = b.alloc_bit();
        b.hmr(a_f, ca);
        let cm = b.alloc_bit();
        b.hmr(m_i, cm);
        let cb = b.alloc_bit();
        b.hmr(b_f, cb);
        // Constant terms: ca·1 + cb·1.
        b.neg_if(ca);
        b.neg_if(cb);
        // (ca ⊕ cm)·u0c.
        for &c in &[ca, cm] {
            b.z_if(u[0], c);
            if let Some(o) = a_prev {
                b.cz_if(o, u[0], c);
                b.cz_if(o, v_w[0], c);
            }
        }
        // (cm ⊕ cb)·u0·v0.
        b.cz_if(u[0], v_w[0], cm);
        b.cz_if(u[0], v_w[0], cb);
        // (ca ⊕ cm)·l·u0·v0: needs the comparator, so it runs only in the
        // shots where the classical parity ca ⊕ cm is 1 (half of them).
        let c = b.alloc_bit();
        b.bit_invert_if(c, ca);
        b.bit_invert_if(c, cm);
        b.set_phase("bk_fused_meas_fixup_cmp");
        b.push_condition(c);
        let q = b.alloc_qubit();
        b.ccx(u[0], v_w[0], q);
        let cmp_width = uv_width(n, iter_idx);
        let l_gt = b.alloc_qubit();
        with_gt_oriented(b, &u[..cmp_width], &v_w[..cmp_width], a_prev, l_gt, |b| {
            b.cz(l_gt, q);
        });
        b.free(l_gt);
        let qm = b.alloc_bit();
        b.hmr(q, qm);
        b.cz_if(u[0], v_w[0], qm);
        b.free(q);
        b.pop_condition();
    } else {
        // Reverse STEP 2 (comparator in orientation a_prev).
        b.set_phase("bk_fused_step2");
        let cmp_width = uv_width(n, iter_idx);
        let l_gt = b.alloc_qubit();
        with_gt_oriented(b, &u[..cmp_width], &v_w[..cmp_width], a_prev, l_gt, |b| {
            b.x(b_f);
            let t = b.alloc_qubit();
            b.ccx(l_gt, b_f, t);
            b.cx(t, m_i);
            b.cx(t, a_f);
            let tm = b.alloc_bit();
            b.hmr(t, tm);
            b.cz_if(l_gt, b_f, tm);
            b.free(t);
            b.x(b_f);
        });
        b.free(l_gt);

        // Reverse STEP 1 (bit-0 reads in orientation a_prev).
        b.set_phase("bk_fused_step1");
        if let Some(o) = a_prev {
            cswap(b, o, u[0], v_w[0]);
        }
        b.cx(m_i, b_f);
        b.cx(a_f, b_f);
        b.x(v_w[0]);
        b.ccx(u[0], v_w[0], m_i);
        b.x(v_w[0]);
        b.cx(u[0], a_f);
        b.x(a_f);
        if let Some(o) = a_prev {
            cswap(b, o, u[0], v_w[0]);
        }
    }

    b.free(add_f);
    b.free(b_f);
    b.free(a_f);
    b.set_phase(_kal_saved_phase);
    a_prev
}

/// H1.A2: `m_i ^= f ∧ [v_C = 0]` in orientation `o`. The physical registers
/// hold (u_C, v_C) or (v_C, u_C); since u_C ≥ 1 at most one of them is zero,
/// so testing both and XORing into m_i equals the canonical test.
/// Self-inverse (used unchanged in the backward pass).
fn step0_zero_test_oriented(
    b: &mut B,
    u: &[QubitId],
    v_w: &[QubitId],
    f: QubitId,
    m_i: QubitId,
    or_width: usize,
    o: Option<QubitId>,
) {
    let flag = b.alloc_qubit();
    with_eq_zero_fast(b, &v_w[0..or_width], flag, |b| {
        b.ccx(f, flag, m_i);
    });
    if o.is_some() {
        with_eq_zero_fast(b, &u[0..or_width], flag, |b| {
            b.ccx(f, flag, m_i);
        });
    }
    b.free(flag);
}

/// Forward ordinary (non-bulk) iteration with fused swaps; same contract as
/// `bulk_iteration_fused_fwd`, with the general step 0/1/2/4/5 that carry `f`.
pub(super) fn iteration_fused_fwd(
    b: &mut B,
    p: U256,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    m_i: QubitId,
    f: QubitId,
    iter_idx: usize,
    a_prev: Option<QubitId>,
) -> QubitId {
    let n = N;
    let a_f = b.alloc_qubit();
    let b_f = b.alloc_qubit();
    let add_f = b.alloc_qubit();

    let _kal_saved_phase = b.phase;
    b.set_phase("kal_fused_step0_eqzero");
    step0_zero_test_oriented(b, u, v_w, f, m_i, uv_width(n, iter_idx), a_prev);
    b.cx(m_i, f);

    b.set_phase("kal_fused_step1");
    if let Some(o) = a_prev {
        cswap(b, o, u[0], v_w[0]);
    }
    b.ccx(f, u[0], b_f); // b_f = f AND u[0] (z)
    b.cx(f, a_f);
    b.cx(b_f, a_f); // a_f = f AND NOT u[0]
    b.x(v_w[0]);
    b.ccx(b_f, v_w[0], m_i);
    b.x(v_w[0]);
    {
        let zm = b.alloc_bit();
        b.hmr(b_f, zm);
        b.cz_if(f, u[0], zm);
    }
    b.cx(a_f, b_f);
    b.cx(m_i, b_f); // b_f = a_f XOR m_i
    if let Some(o) = a_prev {
        cswap(b, o, u[0], v_w[0]);
    }

    b.set_phase("kal_fused_step2");
    let cmp_width = uv_width(n, iter_idx);
    let l_gt = b.alloc_qubit();
    with_gt_oriented(b, &u[..cmp_width], &v_w[..cmp_width], a_prev, l_gt, |b| {
        b.x(b_f);
        b.ccx(f, l_gt, add_f);
        let t = b.alloc_qubit();
        b.ccx(add_f, b_f, t);
        b.cx(t, a_f);
        b.cx(t, m_i);
        {
            let tm = b.alloc_bit();
            b.hmr(t, tm);
            b.cz_if(add_f, b_f, tm);
        }
        b.free(t);
        {
            let am = b.alloc_bit();
            b.hmr(add_f, am);
            b.cz_if(f, l_gt, am);
        }
        b.x(b_f);
    });
    b.free(l_gt);

    b.set_phase("kal_fused_step3_cswap");
    if let Some(o) = a_prev {
        b.cx(o, a_f);
    }
    for j in 0..uv_width(n, iter_idx) {
        cswap(b, a_f, u[j], v_w[j]);
    }
    for j in 0..rs_width_step3(n, iter_idx) {
        cswap(b, a_f, r[j], s[j]);
    }
    if let Some(o) = a_prev {
        b.cx(o, a_f);
        xor_not_s0_oriented(b, a_f, r, s, o);
        b.free(o);
    }

    b.set_phase("kal_fused_step4");
    mcx2_polar(b, f, true, b_f, false, add_f);
    {
        let tmp = b.alloc_qubits(fwd_tmp_width(n, iter_idx));
        let sub_width = uv_width(n, iter_idx);
        let load_width = min_width(n, iter_idx); // add∧u is 0 above this
        for i in 0..load_width {
            b.ccx(add_f, u[i], tmp[i]);
        }
        b.prof("step4:sub_nbit_qq_fast", |b| sub_nbit_qq_fast(b, &tmp[0..sub_width], &v_w[0..sub_width]));
        let transform_width = rs_width_step3(n, iter_idx);
        // u[i] for i >= u.len() is a lazily-unallocated zero bit, where
        // (u ⊕ r) = r, so load add∧r directly.
        let tw_u = transform_width.min(u.len());
        for i in 0..tw_u {
            b.cx(r[i], u[i]);
        }
        for i in 0..transform_width {
            if i < tw_u {
                b.ccx(add_f, u[i], tmp[i]);
            } else {
                b.ccx(add_f, r[i], tmp[i]);
            }
        }
        for i in 0..tw_u {
            b.cx(r[i], u[i]);
        }
        let add_width = rs_width_step9(n, iter_idx);
        let mut tmp_slice: Vec<QubitId> = tmp[0..transform_width].to_vec();
        // add∧r is 0 above transform_width; with fitted widths the s-add can be
        // several bits wider than the load (rs_width_step9 − rs_width_step3 ≥ 1).
        let tmp_pad = b.alloc_qubits(add_width.saturating_sub(transform_width));
        tmp_slice.extend_from_slice(&tmp_pad);
        b.prof("step4:add_nbit_qq_fast", |b| add_nbit_qq_fast(b, &tmp_slice, &s[0..add_width]));
        b.free_vec(&tmp_pad);
        for i in 0..tmp.len() {
            let m = b.alloc_bit();
            b.hmr(tmp[i], m);
            if i < transform_width {
                b.cz_if(add_f, r[i], m);
            } else if i < load_width {
                b.cz_if(add_f, u[i], m);
            }
        }
        b.free_vec(&tmp);
    }

    b.set_phase("kal_fused_step5");
    b.x(b_f);
    {
        let sm = b.alloc_bit();
        b.hmr(add_f, sm);
        b.cz_if(f, b_f, sm);
    }
    b.x(b_f);
    b.cx(m_i, b_f);
    b.cx(a_f, b_f);

    b.set_phase("kal_fused_step6_7_8");
    for i in 0..(v_w.len().min(uv_width(n, iter_idx)) - 1) {
        b.swap(v_w[i], v_w[i + 1]);
    }
    if r_plain_shift(n, iter_idx) {
        mod_double_no_corr(b, r);
    } else {
        mod_double_inplace_fast(b, r, p);
    }

    b.free(add_f);
    b.free(b_f);
    b.set_phase(_kal_saved_phase);
    a_f
}

/// Inverse of `iteration_fused_fwd`.
pub(super) fn iteration_fused_bwd(
    b: &mut B,
    p: U256,
    u: &[QubitId],
    v_w: &[QubitId],
    r: &[QubitId],
    s: &[QubitId],
    m_i: QubitId,
    f: QubitId,
    iter_idx: usize,
    a_f: QubitId,
) -> Option<QubitId> {
    let n = N;
    let b_f = b.alloc_qubit();
    let add_f = b.alloc_qubit();

    let _kal_saved_phase = b.phase;
    b.set_phase("bk_fused_step6_7_8");
    if r_plain_shift(n, iter_idx) {
        mod_halve_no_corr(b, r);
    } else {
        let mut dirty: Vec<QubitId> = u.to_vec();
        dirty.extend_from_slice(v_w);
        mod_halve_inplace_fast_with_dirty(b, r, p, Some(&dirty));
    }
    for i in (0..(v_w.len().min(uv_width(n, iter_idx)) - 1)).rev() {
        b.swap(v_w[i], v_w[i + 1]);
    }

    b.set_phase("bk_fused_step5");
    b.cx(a_f, b_f);
    b.cx(m_i, b_f);
    mcx2_polar(b, f, true, b_f, false, add_f);

    b.set_phase("bk_fused_step4");
    {
        let tmp = b.alloc_qubits(bwd_tmp_width(n, iter_idx));
        let load_width = rs_width_step3(n, iter_idx);
        for i in 0..load_width {
            b.ccx(add_f, r[i], tmp[i]);
        }
        let sub_width = rs_width_step9(n, iter_idx);
        b.prof("step4:sub_nbit_qq_fast", |b| sub_nbit_qq_fast(b, &tmp[0..sub_width], &s[0..sub_width]));
        let transform_width = uv_width(n, iter_idx);
        // add∧u is 0 above mw (u is the smaller operand): there tmp only needs
        // its loaded add∧r cleared, and nothing above the loaded bits.
        let mw = min_width(n, iter_idx);
        // r[i] for i >= r.len() is a lazily-unallocated zero bit: CX(r→u) is a no-op.
        let tw_r = mw.min(r.len());
        for i in 0..tw_r {
            b.cx(r[i], u[i]);
        }
        for i in 0..transform_width {
            if i < mw {
                b.ccx(add_f, u[i], tmp[i]);
            } else if i < load_width {
                b.ccx(add_f, r[i], tmp[i]);
            }
        }
        for i in 0..tw_r {
            b.cx(r[i], u[i]);
        }
        b.prof("step4:add_nbit_qq_fast", |b| add_nbit_qq_fast(b, &tmp[0..transform_width], &v_w[0..transform_width]));
        for i in 0..tmp.len() {
            let m = b.alloc_bit();
            b.hmr(tmp[i], m);
            if i < mw {
                b.cz_if(add_f, u[i], m);
            } else if i >= transform_width && i < load_width {
                b.cz_if(add_f, r[i], m);
            }
        }
        b.free_vec(&tmp);
    }
    b.x(b_f);
    {
        let sm = b.alloc_bit();
        b.hmr(add_f, sm);
        b.cz_if(f, b_f, sm);
    }
    b.x(b_f);

    b.set_phase("bk_fused_step3_cswap");
    let a_prev = if iter_idx > 0 {
        let o = b.alloc_qubit_unreserved(); // carried into the next iteration
        xor_not_s0_oriented(b, a_f, r, s, o);
        b.cx(o, a_f);
        Some(o)
    } else {
        None
    };
    for j in (0..rs_width_step3(n, iter_idx)).rev() {
        cswap(b, a_f, r[j], s[j]);
    }
    for j in (0..uv_width(n, iter_idx)).rev() {
        cswap(b, a_f, u[j], v_w[j]);
    }
    if let Some(o) = a_prev {
        b.cx(o, a_f);
    }

    if H4_MEAS_BWD_FLAGS_REG {
        let o = a_prev.expect("ordinary iterations always follow the bulk prefix");
        let w = uv_width(n, iter_idx);
        // 1. Restore f exactly: the step-0 bit is m0 = ¬F ∧ m on reachable states.
        b.set_phase("bk_fused_meas_flags");
        let g = b.alloc_qubit();
        b.x(f);
        b.ccx(f, m_i, g);
        b.x(f);
        b.cx(g, f); // f = ϕ (value before the forward iteration); g = ϕ·z
        // 2. X-measure a, m, b, g. Their values (u0c canonical bit 0, l = [u>v]):
        //    a = ϕ ⊕ ϕu0c ⊕ ϕ·l·u0v0, m = ϕu0c ⊕ ϕu0v0 ⊕ ϕ·l·u0v0,
        //    b = ϕ ⊕ ϕu0v0, g = ϕ·z. Cancel (−1)^{ca·a + cm·m + cb·b + cg·g}.
        let ca = b.alloc_bit();
        b.hmr(a_f, ca);
        let cm = b.alloc_bit();
        b.hmr(m_i, cm);
        let cb = b.alloc_bit();
        b.hmr(b_f, cb);
        let cg = b.alloc_bit();
        b.hmr(g, cg);
        b.free(g);
        // ϕ·(ca ⊕ cb)
        b.z_if(f, ca);
        b.z_if(f, cb);
        // ϕ·u0v0·(cm ⊕ cb)
        let c2 = b.alloc_bit();
        b.bit_invert_if(c2, cm);
        b.bit_invert_if(c2, cb);
        b.push_condition(c2);
        b.ccz(f, u[0], v_w[0]);
        b.pop_condition();
        // (ϕ·u0c ⊕ ϕ·l·u0v0)·(ca ⊕ cm)
        let c1 = b.alloc_bit();
        b.bit_invert_if(c1, ca);
        b.bit_invert_if(c1, cm);
        b.set_phase("bk_fused_meas_fixup_cmp");
        b.push_condition(c1);
        {
            // mux bit u0c = u0 ⊕ o·(u0 ⊕ v0)
            let mx = b.alloc_qubit();
            b.cx(u[0], mx);
            b.cx(v_w[0], u[0]);
            b.ccx(o, u[0], mx);
            b.cx(v_w[0], u[0]);
            b.cz(f, mx);
            let mm = b.alloc_bit();
            b.hmr(mx, mm);
            b.z_if(u[0], mm);
            b.cz_if(o, u[0], mm);
            b.cz_if(o, v_w[0], mm);
            b.free(mx);
            // ϕ·l·u0v0
            let q = b.alloc_qubit();
            b.ccx(u[0], v_w[0], q);
            let l_gt = b.alloc_qubit();
            with_gt_oriented(b, &u[..w], &v_w[..w], Some(o), l_gt, |b| {
                b.ccz(l_gt, f, q);
            });
            b.free(l_gt);
            let qm = b.alloc_bit();
            b.hmr(q, qm);
            b.cz_if(u[0], v_w[0], qm);
            b.free(q);
        }
        b.pop_condition();
        // ϕ·z·cg, z = [U = 0] ⊕ [V = 0] (exclusive since u_C ≥ 1)
        b.set_phase("bk_fused_meas_fixup_zero");
        b.push_condition(cg);
        {
            let zf = b.alloc_qubit();
            with_eq_zero_fast(b, &v_w[0..w], zf, |b| b.cz(f, zf));
            with_eq_zero_fast(b, &u[0..w], zf, |b| b.cz(f, zf));
            b.free(zf);
        }
        b.pop_condition();
    } else {
        b.set_phase("bk_fused_step2");
        let cmp_width = uv_width(n, iter_idx);
        let l_gt = b.alloc_qubit();
        with_gt_oriented(b, &u[..cmp_width], &v_w[..cmp_width], a_prev, l_gt, |b| {
            b.x(b_f);
            b.ccx(f, l_gt, add_f);
            let t = b.alloc_qubit();
            b.ccx(add_f, b_f, t);
            b.cx(t, m_i);
            b.cx(t, a_f);
            {
                let tm = b.alloc_bit();
                b.hmr(t, tm);
                b.cz_if(add_f, b_f, tm);
            }
            b.free(t);
            {
                let am = b.alloc_bit();
                b.hmr(add_f, am);
                b.cz_if(f, l_gt, am);
            }
            b.x(b_f);
        });
        b.free(l_gt);

        b.set_phase("bk_fused_step1");
        if let Some(o) = a_prev {
            cswap(b, o, u[0], v_w[0]);
        }
        b.cx(m_i, b_f);
        b.cx(a_f, b_f);
        b.ccx(f, u[0], b_f);
        b.x(v_w[0]);
        b.ccx(b_f, v_w[0], m_i);
        b.x(v_w[0]);
        b.cx(b_f, a_f);
        b.cx(f, a_f);
        {
            let zm = b.alloc_bit();
            b.hmr(b_f, zm);
            b.cz_if(f, u[0], zm);
        }
        if let Some(o) = a_prev {
            cswap(b, o, u[0], v_w[0]);
        }

        b.set_phase("bk_fused_step0_eqzero");
        b.cx(m_i, f);
        step0_zero_test_oriented(b, u, v_w, f, m_i, uv_width(n, iter_idx), a_prev);
    }

    b.free(add_f);
    b.free(b_f);
    b.free(a_f);
    b.set_phase(_kal_saved_phase);
    a_prev
}
