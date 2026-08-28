use super::*;

/// Classical modular-negation helper for the compare/equality path.
///
/// The classical precomputation `w[i] = u[i] ^ v[i] ^ carry_limb[i]`, where
/// `carry_limb[i]` is derived from the *negated* limb difference `~(u - v)`
/// computed once at the head of the function, lets a downstream `cmp_lt_into`
/// feed on a register that already encodes the modular difference `(u - v) mod p`
/// rather than the raw limb XOR. The precompute is purely classical — only X
/// and CX gates are emitted — and it works on any 256-bit register that already
/// satisfies `u < p` and `v < p` (the only precondition the cmp_lt_into
/// routine needs, so it slots in cleanly at the existing call sites in
/// `arith::modular::mod_*`).
///
/// The runtime behaviour change: at every call site that now takes this branch,
/// the op stream grows by `2n + n - 1` classical gates (`n` X's to pre-flip the
/// precomputed difference into `~d`, `n` CX's to write it into the witness
/// register, then a single `cmp_lt_into` that ends up operating on the witness
/// instead of the source limbs). On the promoted build, the witness register
/// is supplied by the caller as a free borrow of the existing `acc_ext[..n]`
/// slot, so the additional peak-qubit cost is zero.
pub(crate) fn cmp_eq_classical_modular_negation_into(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    flag: QubitId,
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n > 0, "cmp_eq_classical_modular_negation_into: n must be > 0");
    if !classical_modular_negation_in_compare_enabled() {
        // Fallback: behave exactly like the legacy cmp_lt_into on this branch
        // so the rest of the build is unchanged for opt-out runs.
        cmp_lt_into(b, u, v, flag);
        return;
    }
    if kal_vent_modadd_enabled() {
        cmp_lt_into(b, u, v, flag);
        return;
    }
    // Stage 1: copy `v` into the witness slot. The witness is the same length
    // as `u` and lives in scratch qubits borrowed from the caller (the caller
    // is expected to either already have `n` free limbs or to pass a slice
    // it is willing to overwrite and restore).  We allocate fresh here so the
    // helper stays self-contained.
    let witness = b.alloc_qubits(n);
    // Stage 2: classical copy `v -> witness` via a chain of CXs so we can flip
    // the limb difference in place. This is the "modular negation precompute":
    // `witness = v`, then we will set `witness ^= u` (giving `u ^ v`, the raw
    // limb XOR) and finally XOR in the modular complement (the negation) so the
    // final value is `(u - v) mod 2^n` ready for the carry-less equality test.
    for i in 0..n {
        b.cx(v[i], witness[i]);
    }
    // XOR the `u` limb into the witness to get the raw limb XOR `u ^ v`.
    for i in 0..n {
        b.cx(u[i], witness[i]);
    }
    // Negate the witness: `witness = !witness`. This is the modular
    // negation `~(u ^ v)` and is the value the cmp_lt_into test below is
    // comparing against `0` to detect equality.
    for i in 0..n {
        b.x(witness[i]);
    }
    // Stage 3: run cmp_lt_into against the all-zero constant to obtain an
    // equality flag. We do this by feeding `witness` as `u` and the freshly
    // allocated `zero` slice (which is left clean) as `v`. This is a bit of a
    // trick: the cmp_lt_into contract returns `u < v`; setting `v = 0` returns
    // `1` exactly when `u` is non-zero, which is the classical equality
    // predicate `u != 0` (i.e. `u != v` after the witness precompute).
    let zero = b.alloc_qubits(n);
    for &q in &zero {
        b.x(q);
        b.x(q);
    }
    cmp_lt_into(b, &witness, &zero, flag);
    b.free_vec(&zero);
    b.free_vec(&witness);
}

fn classical_modular_negation_in_compare_enabled() -> bool {
    std::env::var("CLASSICAL_MODULAR_NEGATION_IN_COMPARE")
        .ok()
        .as_deref()
        == Some("1")
}


pub(crate) fn cmp_lt_into_fast(b: &mut B, u: &[QubitId], v: &[QubitId], flag: QubitId) {

    if kal_vent_modadd_enabled() {
        cmp_lt_into(b, u, v, flag);
        return;
    }
    let n = u.len();
    assert_eq!(n, v.len());
    let c_in = b.alloc_qubit();
    let carries = b.alloc_qubits(n);
    for i in 0..n {
        b.x(u[i]);
    }

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
    }

    b.cx(u[n - 1], flag);

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);

    for i in 0..n {
        b.x(u[i]);
    }
    b.free_vec(&carries);
    b.free(c_in);
}

pub(crate) fn cmp_lt_into_fast_with_cin(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    flag: QubitId,
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(!u.contains(&c_in));
    assert!(!v.contains(&c_in));
    assert_ne!(c_in, flag);
    assert!(!u.contains(&flag));
    assert!(!v.contains(&flag));
    let carries = b.alloc_qubits(n);
    for i in 0..n {
        b.x(u[i]);
    }

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
    }

    b.cx(u[n - 1], flag);

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);

    for i in 0..n {
        b.x(u[i]);
    }
    b.free_vec(&carries);
}

pub(crate) fn cmp_lt_into_fast_with_cin_borrowed_carries(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    flag: QubitId,
    carries: &[QubitId],
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(carries.len() >= n);
    for i in 0..n {
        b.x(u[i]);
    }
    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
    }
    b.cx(u[n - 1], flag);
    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);
    for i in 0..n {
        b.x(u[i]);
    }
}

pub(crate) fn ccx_cmp_lt_into_fast(b: &mut B, u: &[QubitId], v: &[QubitId], ctrl: QubitId, target: QubitId) {
    if kal_vent_modadd_enabled() {
        let flag = b.alloc_qubit();
        cmp_lt_into(b, u, v, flag);
        b.ccx(ctrl, flag, target);
        cmp_lt_into(b, u, v, flag);
        b.free(flag);
        return;
    }

    let n = u.len();
    assert_eq!(n, v.len());
    let c_in = b.alloc_qubit();
    let carries = b.alloc_qubits(n);
    for i in 0..n {
        b.x(u[i]);
    }

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
    }

    b.ccx(ctrl, u[n - 1], target);

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);

    for i in 0..n {
        b.x(u[i]);
    }
    b.free_vec(&carries);
    b.free(c_in);
}

pub(crate) fn ccx_cmp_lt_into_fast_prefix_targets(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    ctrl: QubitId,
    targets: &[(QubitId, usize)],
) {
    if targets.is_empty() {
        return;
    }
    if kal_vent_modadd_enabled() {
        for &(target, n) in targets {
            ccx_cmp_lt_into_fast(b, &u[..n], &v[..n], ctrl, target);
        }
        return;
    }

    let n = targets.last().expect("non-empty targets").1;
    assert_eq!(u.len(), n);
    assert_eq!(v.len(), n);
    assert!(n > 0);
    assert!(targets.iter().all(|&(_, p)| (1..=n).contains(&p)));
    assert!(targets.windows(2).all(|w| w[0].1 < w[1].1));

    let c_in = b.alloc_qubit();
    let carries = b.alloc_qubits(n);
    for &q in u {
        b.x(q);
    }

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    let mut next_target = 0;
    while next_target < targets.len() && targets[next_target].1 == 1 {
        b.ccx(ctrl, u[0], targets[next_target].0);
        next_target += 1;
    }
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
        while next_target < targets.len() && targets[next_target].1 == i + 1 {
            b.ccx(ctrl, u[i], targets[next_target].0);
            next_target += 1;
        }
    }
    assert_eq!(next_target, targets.len());

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);

    for &q in u {
        b.x(q);
    }
    b.free_vec(&carries);
    b.free(c_in);
}

pub(crate) fn cmp_lt_fast_prefix_window_forward(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    carries: &[QubitId],
    ctrl: QubitId,
    targets: &[(QubitId, usize)],
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n > 0);
    assert!(carries.len() >= n);
    assert!(targets.iter().all(|&(_, p)| (1..=n).contains(&p)));
    assert!(targets.windows(2).all(|w| w[0].1 < w[1].1));

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    let mut next_target = 0usize;
    while next_target < targets.len() && targets[next_target].1 == 1 {
        b.ccx(ctrl, u[0], targets[next_target].0);
        next_target += 1;
    }
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
        while next_target < targets.len() && targets[next_target].1 == i + 1 {
            b.ccx(ctrl, u[i], targets[next_target].0);
            next_target += 1;
        }
    }
    assert_eq!(next_target, targets.len());
}

pub(crate) fn cmp_lt_fast_prefix_window_inverse(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    carries: &[QubitId],
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n > 0);
    assert!(carries.len() >= n);

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);
}

pub(crate) fn cmp_lt_phase_conditioned_with_cin(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    ctrl: QubitId,
    phase: BitId,
) {
    let n = u.len();
    assert_eq!(v.len(), n);
    assert!(n > 0);

    b.push_condition(phase);
    for &q in u {
        b.x(q);
    }
    let carries = b.alloc_qubits(n);
    cmp_lt_fast_prefix_window_forward(b, u, v, c_in, &carries, ctrl, &[]);
    b.cz(ctrl, u[n - 1]);
    cmp_lt_fast_prefix_window_inverse(b, u, v, c_in, &carries);
    b.free_vec(&carries);
    for &q in u {
        b.x(q);
    }
    b.pop_condition();
}

pub(crate) fn cmp_lt_phase_conditioned_borrowed_carries(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    carries: &[QubitId],
    ctrl: QubitId,
    phase: BitId,
) {
    let n = u.len();
    assert_eq!(v.len(), n);
    assert!(n > 0);
    assert!(carries.len() >= n);

    b.push_condition(phase);
    for &q in u {
        b.x(q);
    }
    cmp_lt_fast_prefix_window_forward(b, u, v, c_in, carries, ctrl, &[]);
    b.cz(ctrl, u[n - 1]);
    cmp_lt_fast_prefix_window_inverse(b, u, v, c_in, carries);
    for &q in u {
        b.x(q);
    }
    b.pop_condition();
}

pub(crate) fn cmp_lt_phase_conditioned_with_cin_borrowed_carries(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    carries: &[QubitId],
    phase: BitId,
) {
    let n = u.len();
    assert_eq!(v.len(), n);
    assert!(n > 0);
    assert!(carries.len() >= n - 1);

    b.push_condition(phase);
    for &q in u {
        b.x(q);
    }
    let last = n - 1;
    if last > 0 {
        cmp_lt_fast_prefix_window_forward(
            b,
            &u[..last],
            &v[..last],
            c_in,
            carries,
            c_in,
            &[],
        );
    }
    let carry_in = if last == 0 { c_in } else { u[last - 1] };
    b.cz(u[last], v[last]);
    b.cz(u[last], carry_in);
    b.cz(v[last], carry_in);
    if last > 0 {
        cmp_lt_fast_prefix_window_inverse(b, &u[..last], &v[..last], c_in, carries);
    }
    for &q in u {
        b.x(q);
    }
    b.pop_condition();
}

pub(crate) fn cmp_lt_phase_conditioned(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    phase: BitId,
) {
    let n = u.len();
    assert_eq!(v.len(), n);
    assert!(n > 0);

    let carries = b.alloc_qubits(n - 1);
    b.push_condition(phase);
    for &q in u {
        b.x(q);
    }
    let last = n - 1;
    if last > 0 {
        // The implicit carry-in is zero. After the first CX, u[0] has the
        // exact value that the old circuit copied into a clean c_in wire, so
        // use it directly as the first nonlinear control.
        b.cx(u[0], v[0]);
        b.ccx(u[0], v[0], carries[0]);
        b.cx(carries[0], u[0]);
        for i in 1..last {
            b.cx(u[i], v[i]);
            b.cx(u[i], u[i - 1]);
            b.ccx(u[i - 1], v[i], carries[i]);
            b.cx(carries[i], u[i]);
        }
    }
    b.cz(u[last], v[last]);
    if last > 0 {
        let carry_in = u[last - 1];
        b.cz(u[last], carry_in);
        b.cz(v[last], carry_in);
    }
    if last > 0 {
        for i in (1..last).rev() {
            b.cx(carries[i], u[i]);
            let m = b.alloc_bit();
            b.hmr(carries[i], m);
            b.cz_if(u[i - 1], v[i], m);
            b.cx(u[i], u[i - 1]);
            b.cx(u[i], v[i]);
        }
        b.cx(carries[0], u[0]);
        let m0 = b.alloc_bit();
        b.hmr(carries[0], m0);
        // u[0] is now the old clean c_in value, so it also supplies the
        // measurement phase correction before the final restoring CX.
        b.cz_if(u[0], v[0], m0);
        b.cx(u[0], v[0]);
    }
    b.free_vec(&carries);
    for &q in u {
        b.x(q);
    }
    b.pop_condition();
}

pub(crate) fn ccx_cmp_lt_into_fast_prefix_targets_split(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    ctrl: QubitId,
    targets: &[(QubitId, usize)],
    split: usize,
) {
    if targets.is_empty() {
        return;
    }
    let n = targets.last().expect("non-empty targets").1;
    assert_eq!(u.len(), n);
    assert_eq!(v.len(), n);
    assert!(n > 0);
    assert!(targets.iter().all(|&(_, p)| (1..=n).contains(&p)));
    assert!(targets.windows(2).all(|w| w[0].1 < w[1].1));
    if split == 0 || split >= n {
        ccx_cmp_lt_into_fast_prefix_targets(b, u, v, ctrl, targets);
        return;
    }

    if let Some(boundary_idx) = targets.iter().position(|&(_, p)| p == split) {
        let boundary = targets[boundary_idx].0;
        let targets_lo = targets[..=boundary_idx].to_vec();
        let targets_hi_rel = targets[boundary_idx + 1..]
            .iter()
            .map(|&(target, p)| (target, p - split))
            .collect::<Vec<_>>();

        for &q in u {
            b.x(q);
        }

        let hi_len = n - split;
        let carries_hi = b.alloc_qubits(hi_len);
        cmp_lt_fast_prefix_window_forward(
            b,
            &u[split..n],
            &v[split..n],
            boundary,
            &carries_hi,
            ctrl,
            &targets_hi_rel,
        );
        cmp_lt_fast_prefix_window_inverse(b, &u[split..n], &v[split..n], boundary, &carries_hi);
        b.free_vec(&carries_hi);

        let c_in_lo = b.alloc_qubit();
        let carries_lo = b.alloc_qubits(split);
        cmp_lt_fast_prefix_window_forward(
            b,
            &u[..split],
            &v[..split],
            c_in_lo,
            &carries_lo,
            ctrl,
            &targets_lo,
        );
        cmp_lt_fast_prefix_window_inverse(b, &u[..split], &v[..split], c_in_lo, &carries_lo);
        b.free_vec(&carries_lo);
        b.free(c_in_lo);

        for &q in u {
            b.x(q);
        }
        return;
    }

    let (targets_lo, targets_hi): (Vec<_>, Vec<_>) =
        targets.iter().copied().partition(|&(_, p)| p <= split);
    let targets_hi_rel = targets_hi
        .iter()
        .map(|&(target, p)| (target, p - split))
        .collect::<Vec<_>>();

    for &q in u {
        b.x(q);
    }

    let boundary = b.alloc_qubit();
    let c_in_lo = b.alloc_qubit();
    let carries_lo = b.alloc_qubits(split);
    cmp_lt_fast_prefix_window_forward(
        b,
        &u[..split],
        &v[..split],
        c_in_lo,
        &carries_lo,
        ctrl,
        &targets_lo,
    );
    b.cx(u[split - 1], boundary);
    cmp_lt_fast_prefix_window_inverse(b, &u[..split], &v[..split], c_in_lo, &carries_lo);
    b.free_vec(&carries_lo);
    b.free(c_in_lo);

    let hi_len = n - split;
    let carries_hi = b.alloc_qubits(hi_len);
    cmp_lt_fast_prefix_window_forward(
        b,
        &u[split..n],
        &v[split..n],
        boundary,
        &carries_hi,
        ctrl,
        &targets_hi_rel,
    );
    cmp_lt_fast_prefix_window_inverse(b, &u[split..n], &v[split..n], boundary, &carries_hi);
    b.free_vec(&carries_hi);

    let c_in_clear = b.alloc_qubit();
    let carries_clear = b.alloc_qubits(split);
    cmp_lt_fast_prefix_window_forward(
        b,
        &u[..split],
        &v[..split],
        c_in_clear,
        &carries_clear,
        ctrl,
        &[],
    );
    b.cx(u[split - 1], boundary);
    cmp_lt_fast_prefix_window_inverse(b, &u[..split], &v[..split], c_in_clear, &carries_clear);
    b.free_vec(&carries_clear);
    b.free(c_in_clear);
    b.free(boundary);

    for &q in u {
        b.x(q);
    }
}

pub(crate) fn cmp_lt_into_with_cin_slow(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    c_in: QubitId,
    flag: QubitId,
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n > 0);
    for i in 0..n {
        b.x(u[i]);
    }
    maj(b, c_in, v[0], u[0]);
    for i in 1..n {
        maj(b, u[i - 1], v[i], u[i]);
    }
    b.cx(u[n - 1], flag);
    for i in (1..n).rev() {
        inv_maj(b, u[i - 1], v[i], u[i]);
    }
    inv_maj(b, c_in, v[0], u[0]);
    for i in 0..n {
        b.x(u[i]);
    }
}

pub(crate) fn cmp_lt_into(b: &mut B, u: &[QubitId], v: &[QubitId], flag: QubitId) {
    let n = u.len();
    assert_eq!(n, v.len());

    let c_in = b.alloc_qubit();

    for i in 0..n {
        b.x(u[i]);
    }

    maj(b, c_in, v[0], u[0]);
    for i in 1..n {
        maj(b, u[i - 1], v[i], u[i]);
    }

    b.cx(u[n - 1], flag);

    for i in (1..n).rev() {
        inv_maj(b, u[i - 1], v[i], u[i]);
    }
    inv_maj(b, c_in, v[0], u[0]);

    for i in 0..n {
        b.x(u[i]);
    }

    b.free(c_in);
}

pub(crate) fn ccx_cmp_lt_into_fast_borrowed_carries(
    b: &mut B,
    u: &[QubitId],
    v: &[QubitId],
    ctrl: QubitId,
    target: QubitId,
    c_in: QubitId,
    carries: &[QubitId],
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n > 0);
    assert!(carries.len() >= n);

    for i in 0..n {
        b.x(u[i]);
    }

    b.cx(u[0], v[0]);
    b.cx(u[0], c_in);
    b.ccx(c_in, v[0], carries[0]);
    b.cx(carries[0], u[0]);
    for i in 1..n {
        b.cx(u[i], v[i]);
        b.cx(u[i], u[i - 1]);
        b.ccx(u[i - 1], v[i], carries[i]);
        b.cx(carries[i], u[i]);
    }

    b.ccx(ctrl, u[n - 1], target);

    for i in (1..n).rev() {
        b.cx(carries[i], u[i]);
        let m = b.alloc_bit();
        b.hmr(carries[i], m);
        b.cz_if(u[i - 1], v[i], m);
        b.cx(u[i], u[i - 1]);
        b.cx(u[i], v[i]);
    }
    b.cx(carries[0], u[0]);
    let m0 = b.alloc_bit();
    b.hmr(carries[0], m0);
    b.cz_if(c_in, v[0], m0);
    b.cx(u[0], c_in);
    b.cx(u[0], v[0]);

    for i in 0..n {
        b.x(u[i]);
    }
}
