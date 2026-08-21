use super::*;

/// Fixed-depth ping-pong division.  The value walk records one sign qubit per
/// round; the coefficient pass consumes that log once, then the reverse value
/// walk restores the denominator and clears the log.
const ROUNDS_DEFAULT: usize = 704;
const VALUE_WIDTH: usize = N + 3;

/// Fixed depth of the ping-pong walk.  The tape carries one sign qubit per
/// round and is fully live during the coefficient replay, so this sets both the
/// dominant term in peak width and (near-linearly) the gate count.  Lowering it
/// only stays correct while the recurrence still converges.
fn rounds_for(direction: PingPongDirection) -> usize {
    match direction {
        PingPongDirection::Divide => rounds(),
        PingPongDirection::Multiply => {
            // One round fewer on the multiply traversal: its fused doubling
            // cell holds one more wire (the shifted-out top bit) during the
            // chunked add than the divide cell does, so a one-bit shorter
            // tape puts both replay peaks at the same width.  Convergence
            // exposure of one round on one traversal is ~+0.05 lambda.
            static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
            tuned_window("SUB4_PP_ROUNDS_MUL", &SLOT, rounds())
        }
    }
}

fn rounds() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    // 700, not 704: the walk's convergence tail tolerates the four-round cut on
    // this draw (validated 9,024/9,024 with the baked tail nonce), the tape gives
    // back four sign qubits against two wider terminal wires (peak 1320 -> 1318),
    // and each cut round saves its replay and walk adds on both traversals.
    tuned_window("SUB4_PP_ROUNDS", &SLOT, 700)
}

/// When set, the width schedule is compressed so it still reaches its floor on
/// the final round at a reduced depth, instead of stopping short.
fn width_round_index(round: usize) -> usize {
    if std::env::var_os("SUB4_PP_WIDTH_RESCALE").is_none() {
        return round;
    }
    let r = rounds();
    if r <= 1 {
        return round;
    }
    round * (ROUNDS_DEFAULT - 1) / (r - 1)
}
/// Truncation windows for the measured-erasure repairs.  Each one trades
/// emitted Toffoli against the intrinsic mismatch rate, so they are swept as a
/// group; the defaults are the shipped values.
fn tuned_window(name: &str, slot: &'static std::sync::OnceLock<usize>, default: usize) -> usize {
    *slot.get_or_init(|| {
        std::env::var(name)
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(default)
    })
}

fn replay_chunk() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    tuned_window("SUB4_PP_REPLAY_CHUNK", &SLOT, 96)
}

fn replay_chunk_compare() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    tuned_window("SUB4_PP_REPLAY_CHUNK_COMPARE", &SLOT, 23)
}

fn replay_fold_window() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    tuned_window("SUB4_PP_REPLAY_FOLD_WINDOW", &SLOT, 54)
}

/// 54, not 55: the fold carry chain is `min(n-2, highest_set_bit(c) + window)`
/// long, so one position off the window is exactly one fewer carry ancilla at
/// the binding allocation, which is what takes peak width 1321 -> 1320.  The
/// dropped position only matters when a carry would have propagated that far,
/// which the tail nonce absorbs.
fn endpoint_fold_window() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    tuned_window("SUB4_PP_ENDPOINT_FOLD_WINDOW", &SLOT, 40)
}

fn replay_flag_compare() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    tuned_window("SUB4_PP_REPLAY_FLAG_COMPARE", &SLOT, 24)
}

/// Translate the source model's `lsbs = 56` literally: its pseudo-Mersenne
/// corrections operate on `acc[..lsbs]`, whereas the target helper's `window`
/// argument means that many positions *after* the constant's top bit.
fn replay_fold_target(target: &[QubitId]) -> &[QubitId] {
    if std::env::var_os("SUB4_PINGPONG_LOW56_FOLD").is_some() {
        &target[..replay_fold_window()]
    } else {
        target
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PingPongDirection {
    Divide,
    Multiply,
}

/// `numerator *= denominator^-1` for [`PingPongDirection::Divide`], or
/// `numerator *= denominator` for [`PingPongDirection::Multiply`].
///
/// Both caller registers are preserved in place except for the documented
/// numerator result.  The shrinking walk lends its cleared high wires to the
/// tape and scratch allocator.  [`restore_wire_layout`] puts the restored
/// value back onto the original ABI wires before returning.
pub(crate) fn pingpong_mod_mul_div_in_place(
    b: &mut B,
    denominator: &[QubitId],
    numerator: &[QubitId],
    direction: PingPongDirection,
) {
    assert_eq!(denominator.len(), N);
    assert_eq!(numerator.len(), N);

    let mut u = load_const(b, N, SECP256K1_P);
    u.extend(b.alloc_qubits(VALUE_WIDTH - N));
    let wanted_u = u.clone();
    let mut v = denominator.to_vec();
    v.extend(b.alloc_qubits(VALUE_WIDTH - N));
    let wanted_v = v.clone();

    let recompute_lift = std::env::var_os("SUB4_PINGPONG_KEEP_ODD_LIFT").is_none();
    let even_lift = if fused_lift_round0_enabled() {
        None
    } else {
        // Ping-pong's signed recurrence requires both values odd.  Lift an even
        // denominator to the congruent negative representative a-p; keep the one
        // lift bit so the exact caller value can be restored after the walk.
        let q = b.alloc_qubit();
        b.x(q);
        b.cx(denominator[0], q);
        csub_nbit_const_direct_fast(b, &v, SECP256K1_P, q);
        if recompute_lift {
            b.cx(v[VALUE_WIDTH - 1], q);
            b.free(q);
        }
        Some(q)
    };

    b.set_phase(match direction {
        PingPongDirection::Divide => "pp_div_walk",
        PingPongDirection::Multiply => "pp_mul_walk",
    });
    let tape = value_walk(b, &mut u, &mut v, rounds_for(direction));
    b.set_phase(match direction {
        PingPongDirection::Divide => "pp_div_replay",
        PingPongDirection::Multiply => "pp_mul_replay",
    });
    let coefficient = b.alloc_qubits(N);

    // The fixed walk terminates with each signed value equal to +1 or -1.
    // Therefore the penultimate bit is a copy of the sign bit.  It is idle
    // throughout coefficient replay, which only observes the terminal sign,
    // so clear and release this passenger across the replay peak.  Every
    // scratch user returns it to |0>; reacquire and restore the sign extension
    // before the reverse value walk consumes the terminal register again.
    // Generalised passenger loan: at the terminal state every bit of u and v
    // below the sign is a copy of the sign (two's-complement +1 / -1), and
    // bit 0 is the constant 1 (both values stay odd).  All of them are idle
    // across the replay, which reads only the two sign wires.
    let terminal_sign = u[u.len() - 1];
    let terminal_sign_v = v[v.len() - 1];
    let loan_all = std::env::var_os("SUB4_PP_LOAN_ONE").is_none();
    let mut loans: Vec<(QubitId, Option<QubitId>)> = Vec::new();
    if loan_all {
        for reg in [&u, &v] {
            let sign = reg[reg.len() - 1];
            for i in 1..reg.len() - 1 {
                b.cx(sign, reg[i]);
                b.free(reg[i]);
                loans.push((reg[i], Some(sign)));
            }
            b.x(reg[0]);
            b.free(reg[0]);
            loans.push((reg[0], None));
        }
    } else {
        let replay_loan = u[u.len() - 2];
        b.cx(terminal_sign, replay_loan);
        b.free(replay_loan);
        loans.push((replay_loan, Some(terminal_sign)));
    }
    let _ = terminal_sign_v;

    match direction {
        PingPongDirection::Divide => {
            // The emitted seed is genuinely (0,c), not a cost-model comment:
            // `coefficient` is fresh |0> and `numerator` is the caller's c.
            replay_halving(b, &tape, &coefficient, numerator);

            // At the terminal state both coefficient registers hold c/a, with
            // the signs of terminal u and v respectively.  Canonicalise them,
            // then use their equality to clean the redundant register.
            conditional_mod_negate(b, u[u.len() - 1], &coefficient);
            conditional_mod_negate(b, v[v.len() - 1], numerator);
            for i in 0..N {
                b.cx(numerator[i], coefficient[i]);
            }
        }
        PingPongDirection::Multiply => {
            // Seed the inverse recurrence at the terminal pair
            // (sign(u)c, sign(v)c), then undo the coefficient walk.  This is
            // multiplication, not a second halving replay.
            for i in 0..N {
                b.cx(numerator[i], coefficient[i]);
            }
            conditional_mod_negate(b, u[u.len() - 1], &coefficient);
            conditional_mod_negate(b, v[v.len() - 1], numerator);
            replay_doubling_inverse(b, &tape, &coefficient, numerator);
        }
    }

    for &(q, sign) in loans.iter().rev() {
        b.reacquire(q);
        match sign {
            Some(sign) => b.cx(sign, q),
            None => b.x(q),
        }
    }

    // Divide leaves two equal canonical outputs and clears one above;
    // multiply's inverse recurrence ends at (0,a*c).  Either way this is a
    // proved-zero register, never a fake free.
    b.free_vec(&coefficient);
    b.set_phase(match direction {
        PingPongDirection::Divide => "pp_div_walkback",
        PingPongDirection::Multiply => "pp_mul_walkback",
    });
    value_walk_back(b, &mut u, &mut v, tape);
    b.set_phase(match direction {
        PingPongDirection::Divide => "pp_div_restore",
        PingPongDirection::Multiply => "pp_mul_restore",
    });
    if let Some(even_lift) = even_lift {
        let even_lift = if recompute_lift {
            let q = b.alloc_qubit();
            b.cx(v[VALUE_WIDTH - 1], q);
            q
        } else {
            even_lift
        };
        cadd_nbit_const_direct_fast(b, &v, SECP256K1_P, even_lift);
        b.cx(denominator[0], even_lift);
        b.x(even_lift);
        b.free(even_lift);
    }
    restore_wire_layout(b, &mut u, &mut v, &wanted_u, &wanted_v);

    b.free_vec(&v[N..]);
    for i in 0..N {
        if SECP256K1_P.bit(i) {
            b.x(u[i]);
        }
    }
    b.free_vec(&u);
}

/// Restore the compile-time register identity after streamed high wires have
/// served as tape.  If a wanted wire is currently free, swap the semantic bit
/// into it and return the now-zero displaced wire to the allocator.
fn restore_wire_layout(
    b: &mut B,
    u: &mut [QubitId],
    v: &mut [QubitId],
    wanted_u: &[QubitId],
    wanted_v: &[QubitId],
) {
    let mut current: Vec<QubitId> = u.iter().chain(v.iter()).copied().collect();
    let wanted: Vec<QubitId> = wanted_u.iter().chain(wanted_v.iter()).copied().collect();
    assert_eq!(current.len(), wanted.len());

    for i in 0..current.len() {
        let want = wanted[i];
        if current[i] == want {
            continue;
        }
        if let Some(j) = current[i + 1..].iter().position(|&q| q == want) {
            let j = i + 1 + j;
            b.swap(current[i], current[j]);
            current.swap(i, j);
        } else {
            b.reacquire(want);
            b.swap(current[i], want);
            b.free(current[i]);
            current[i] = want;
        }
    }

    u.copy_from_slice(&current[..u.len()]);
    v.copy_from_slice(&current[u.len()..]);
    debug_assert_eq!(u, wanted_u);
    debug_assert_eq!(v, wanted_v);
}

fn value_width(round: usize) -> usize {
    const BREAK_1: usize = 40;
    const BREAK_2: usize = 304;
    const SLOPE_1: usize = 17;
    const SLOPE_2: usize = 33;
    const SLOPE_3: usize = 40;
    const MARGIN: usize = 4;

    let start = N + MARGIN;
    let round = width_round_index(round);
    let width = if round < BREAK_1 {
        start.saturating_sub(SLOPE_1 * round / 100)
    } else {
        let at_first = start.saturating_sub(SLOPE_1 * BREAK_1 / 100);
        if round < BREAK_2 {
            at_first.saturating_sub(SLOPE_2 * (round - BREAK_1) / 100)
        } else {
            let at_second = at_first.saturating_sub(SLOPE_2 * (BREAK_2 - BREAK_1) / 100);
            at_second.saturating_sub(SLOPE_3 * (round - BREAK_2) / 100)
        }
    };
    width.clamp(8, VALUE_WIDTH)
}

fn fused_lift_round0_enabled() -> bool {
    std::env::var_os("SUB4_PINGPONG_SEPARATE_LIFT").is_none()
}

fn mux_round0_correction_enabled() -> bool {
    std::env::var_os("SUB4_PINGPONG_SPLIT_ROUND0").is_none()
}

fn mux_round0_correction(
    b: &mut B,
    value: &[QubitId],
    not_a1: QubitId,
    a0: QubitId,
    subtract: bool,
) {
    let both = and_clean(b, not_a1, a0);
    let not_a1_xor_a0 = b.alloc_qubit();
    b.cx(not_a1, not_a1_xor_a0);
    b.cx(a0, not_a1_xor_a0);
    let a0_xor_both = b.alloc_qubit();
    b.cx(a0, a0_xor_both);
    b.cx(both, a0_xor_both);

    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let h = f.wrapping_sub(U256::from(1)) >> 1;
    let minus_h = U256::ZERO.wrapping_sub(h);
    let half_f_plus_one = f.wrapping_sub(h);
    let controls: Vec<Option<QubitId>> = (0..N)
        .map(|i| {
            let x = f.bit(i);
            let y = minus_h.bit(i);
            let xy = half_f_plus_one.bit(i) ^ x ^ y;
            match (x, y, xy) {
                (false, false, false) => None,
                (true, false, false) => Some(not_a1),
                (false, true, false) => Some(a0),
                (false, false, true) => Some(both),
                (true, true, false) => Some(not_a1_xor_a0),
                (false, true, true) => Some(a0_xor_both),
                _ => unreachable!("secp256k1 round-zero selector pattern"),
            }
        })
        .collect();
    if subtract {
        csub_per_position_controls_trunc(b, value, &controls, N - 2);
    } else {
        cadd_per_position_controls_trunc(b, value, &controls, N - 2);
    }

    b.cx(both, a0_xor_both);
    b.cx(a0, a0_xor_both);
    b.free(a0_xor_both);
    b.cx(a0, not_a1_xor_a0);
    b.cx(not_a1, not_a1_xor_a0);
    b.free(not_a1_xor_a0);
    and_uncompute(b, both, not_a1, a0);
}

/// Fuse the odd lift `a -= (!a0)*p` with ping-pong's first add and shift.
/// With `p = 2^N-f`, `h=(f-1)/2`, and `q=floor(a/2)`, the four low-bit arms are
/// one sparse map: `q - p + a1*p + a0*(p+1)/2`.
fn fused_lift_round0_forward(b: &mut B, v: &[QubitId]) -> QubitId {
    debug_assert_eq!(v.len(), VALUE_WIDTH);
    let a0 = b.alloc_qubit();
    b.cx(v[0], a0);
    for i in 0..VALUE_WIDTH - 1 {
        b.swap(v[i], v[i + 1]);
    }
    b.cx(a0, v[VALUE_WIDTH - 1]);

    let not_a1 = b.alloc_qubit();
    b.x(not_a1);
    b.cx(v[0], not_a1);
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let h = f.wrapping_sub(U256::from(1)) >> 1;
    if mux_round0_correction_enabled() {
        mux_round0_correction(b, &v[..N], not_a1, a0, false);
    } else {
        cadd_nbit_const_direct_fast(b, &v[..N], f, not_a1);
    }
    for &q in &v[N..] {
        b.cx(not_a1, q);
    }
    if !mux_round0_correction_enabled() {
        csub_nbit_const_direct_fast(b, &v[..N], h, a0);
    }
    b.cx(a0, v[N - 1]);

    // The four output ranges are disjoint: a1=0 is negative and a1=1 positive.
    b.cx(v[VALUE_WIDTH - 1], not_a1);
    b.free(not_a1);
    a0
}

fn fused_lift_round0_reverse(b: &mut B, v: &[QubitId], a0: QubitId) {
    debug_assert_eq!(v.len(), VALUE_WIDTH);
    if std::env::var_os("SUB4_PINGPONG_SEPARATE_ENDPOINT").is_none() {
        return fused_lift_round0_reverse_sparse(b, v, a0);
    }
    let not_a1 = b.alloc_qubit();
    b.cx(v[VALUE_WIDTH - 1], not_a1);
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let h = f.wrapping_sub(U256::from(1)) >> 1;

    b.cx(a0, v[N - 1]);
    if !mux_round0_correction_enabled() {
        cadd_nbit_const_direct_fast(b, &v[..N], h, a0);
    }
    for &q in &v[N..] {
        b.cx(not_a1, q);
    }
    if mux_round0_correction_enabled() {
        mux_round0_correction(b, &v[..N], not_a1, a0, true);
    } else {
        csub_nbit_const_direct_fast(b, &v[..N], f, not_a1);
    }

    b.cx(a0, v[VALUE_WIDTH - 1]);
    for i in (0..VALUE_WIDTH - 1).rev() {
        b.swap(v[i], v[i + 1]);
    }
    b.cx(v[1], not_a1);
    b.x(not_a1);
    b.free(not_a1);
    b.cx(v[0], a0);
    b.free(a0);
}

/// Recover the canonical denominator from the signed round-zero half-state
/// with one short pseudo-Mersenne carry chain.  If `w` is that state, then
/// `2w = a + k*p`, where `k = a0 - 2*!a1`.  Since `p = 2^256-f`, the low word
/// of `2w` needs only the sparse correction `k*f`.
fn fused_lift_round0_reverse_sparse(b: &mut B, v: &[QubitId], a0: QubitId) {
    let not_a1 = b.alloc_qubit();
    b.cx(v[VALUE_WIDTH - 1], not_a1);

    // Arithmetic left shift in the signed 259-bit envelope.  The discarded
    // sign copy is redundant; the three new high bits are (a0,!a1,!a1).
    b.cx(not_a1, v[VALUE_WIDTH - 1]);
    for i in (0..VALUE_WIDTH - 1).rev() {
        b.swap(v[i], v[i + 1]);
    }

    // k*f is +a0*f when !a1=0 and -(2-a0)*f otherwise.  A complement
    // sandwich turns both signs into one selected-magnitude addition.
    let both = and_clean(b, not_a1, a0);
    let not_a1_and_not_a0 = b.alloc_qubit();
    b.cx(not_a1, not_a1_and_not_a0);
    b.cx(both, not_a1_and_not_a0);
    let selector_xor = b.alloc_qubit();
    b.cx(a0, selector_xor);
    b.cx(not_a1_and_not_a0, selector_xor);
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let controls: Vec<Option<QubitId>> = (0..N)
        .map(|i| match (f.bit(i), i > 0 && f.bit(i - 1)) {
            (false, false) => None,
            (true, false) => Some(a0),
            (false, true) => Some(not_a1_and_not_a0),
            (true, true) => Some(selector_xor),
        })
        .collect();
    for &q in &v[..N] {
        b.cx(not_a1, q);
    }
    cadd_per_position_controls_trunc(b, &v[..N], &controls, replay_fold_window() - 2);
    for &q in &v[..N] {
        b.cx(not_a1, q);
    }
    b.cx(not_a1_and_not_a0, selector_xor);
    b.cx(a0, selector_xor);
    b.free(selector_xor);
    b.cx(both, not_a1_and_not_a0);
    b.cx(not_a1, not_a1_and_not_a0);
    b.free(not_a1_and_not_a0);
    and_uncompute(b, both, not_a1, a0);

    b.cx(a0, v[N]);
    b.cx(not_a1, v[N + 1]);
    b.cx(not_a1, v[N + 2]);
    b.cx(v[1], not_a1);
    b.x(not_a1);
    b.free(not_a1);
    b.cx(v[0], a0);
    b.free(a0);
}

/// Ping-pong's wrapped signed add with its first two carries supplied linearly.
///
/// PRECONDITION: both walk operands are odd, `sign = target[1] ^ source[1]`,
/// and `target0_is_one` describes the target before the complement sandwich.
/// Then the wrapped carry bits are `c1 = sign ^ target[0]` and
/// `c2 = source[1]`, so the first two ANDs of the generic chain are unnecessary.
fn signed_add_wrapping_sigma(
    b: &mut B,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
) {
    let n = source.len();
    assert_eq!(n, target.len());
    if n < 4 {
        for &q in target {
            b.cx(sign, q);
        }
        add_nbit_qq_fast(b, source, target);
        for &q in target {
            b.cx(sign, q);
        }
        return;
    }

    for &q in target {
        b.cx(sign, q);
    }
    let carries = b.alloc_qubits(n - 1);

    b.cx(sign, carries[0]);
    if target0_is_one {
        b.x(carries[0]);
    }
    b.cx(source[1], carries[1]);
    b.cx(carries[0], source[1]);
    b.cx(carries[0], target[1]);

    for i in 2..n - 1 {
        b.cx(carries[i - 1], source[i]);
        b.cx(carries[i - 1], target[i]);
        b.ccx(source[i], target[i], carries[i]);
        b.cx(carries[i - 1], carries[i]);
    }

    b.cx(carries[n - 2], target[n - 1]);
    b.cx(source[n - 1], target[n - 1]);

    for i in (2..n - 1).rev() {
        b.cx(carries[i - 1], carries[i]);
        let measured = b.alloc_bit();
        b.hmr(carries[i], measured);
        b.cz_if(source[i], target[i], measured);
        b.cx(carries[i - 1], source[i]);
        b.cx(source[i], target[i]);
    }

    b.cx(carries[0], source[1]);
    b.cx(source[1], carries[1]);
    b.cx(source[1], target[1]);
    if target0_is_one {
        b.x(carries[0]);
    }
    b.cx(sign, carries[0]);
    b.cx(source[0], target[0]);
    b.free_vec(&carries);

    for &q in target {
        b.cx(sign, q);
    }
}

fn signed_add_wrapping(
    b: &mut B,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
) {
    if std::env::var_os("SUB4_PINGPONG_GENERIC_WALK").is_none() {
        return signed_add_wrapping_sigma(b, sign, source, target, target0_is_one);
    }
    for &q in target {
        b.cx(sign, q);
    }
    add_nbit_qq_fast(b, source, target);
    for &q in target {
        b.cx(sign, q);
    }
}

fn value_walk(b: &mut B, u: &mut Vec<QubitId>, v: &mut Vec<QubitId>, rounds: usize) -> Vec<QubitId> {
    let mut tape = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let width = value_width(round);
        while u.len() > width {
            let (lu, lv) = (u.len(), v.len());
            b.cx(u[lu - 2], u[lu - 1]);
            b.cx(v[lv - 2], v[lv - 1]);
            b.free(u.pop().expect("u has the scheduled width"));
            b.free(v.pop().expect("v has the scheduled width"));
        }

        if round == 0 && fused_lift_round0_enabled() {
            tape.push(fused_lift_round0_forward(b, v));
            continue;
        }

        let (source, target) = if round.is_multiple_of(2) {
            (&u[..width], &v[..width])
        } else {
            (&v[..width], &u[..width])
        };
        let sign = b.alloc_qubit();
        b.cx(target[1], sign);
        b.cx(source[1], sign);
        signed_add_wrapping(b, sign, source, target, true);
        tape.push(sign);

        for i in 0..width - 1 {
            b.swap(target[i], target[i + 1]);
        }
        b.cx(target[width - 2], target[width - 1]);
    }
    tape
}

fn value_walk_back(b: &mut B, u: &mut Vec<QubitId>, v: &mut Vec<QubitId>, tape: Vec<QubitId>) {
    let rounds = tape.len();
    for elapsed in 0..rounds {
        let round = rounds - 1 - elapsed;
        let width = value_width(round);
        while u.len() < width {
            let next_u = b.alloc_qubit();
            let next_v = b.alloc_qubit();
            b.cx(u[u.len() - 1], next_u);
            b.cx(v[v.len() - 1], next_v);
            u.push(next_u);
            v.push(next_v);
        }


        if round == 0 && fused_lift_round0_enabled() {
            fused_lift_round0_reverse(b, v, tape[round]);
            continue;
        }

        let sign = tape[round];
        let (source, target) = if round.is_multiple_of(2) {
            (&u[..width], &v[..width])
        } else {
            (&v[..width], &u[..width])
        };
        b.cx(target[width - 2], target[width - 1]);
        for i in (0..width - 1).rev() {
            b.swap(target[i], target[i + 1]);
        }
        b.x(sign);
        signed_add_wrapping(b, sign, source, target, false);
        b.x(sign);
        b.cx(target[1], sign);
        b.cx(source[1], sign);
        b.free(sign);
    }

    while u.len() < VALUE_WIDTH {
        let next_u = b.alloc_qubit();
        let next_v = b.alloc_qubit();
        b.cx(u[u.len() - 1], next_u);
        b.cx(v[v.len() - 1], next_v);
        u.push(next_u);
        v.push(next_v);
    }
}

fn conditional_mod_negate(b: &mut B, control: QubitId, value: &[QubitId]) {
    for &q in value {
        b.cx(control, q);
    }
    // ~(x) - (f-1) = p-x for p=2^256-f.  The sparse low correction avoids a
    // register-wide constant-add workspace.  As elsewhere in this benchmark,
    // the carry window is the deliberately measured approximation.
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    csub_nbit_const_direct_trunc_fast(
        b,
        replay_fold_target(value),
        f.wrapping_sub(U256::from(1)),
        control,
        endpoint_fold_window(),
    );
}

fn and_clean(b: &mut B, a: QubitId, c: QubitId) -> QubitId {
    let out = b.alloc_qubit();
    b.ccx(a, c, out);
    out
}

fn and_uncompute(b: &mut B, out: QubitId, a: QubitId, c: QubitId) {
    let measured = b.alloc_bit();
    b.hmr(out, measured);
    b.cz_if(a, c, measured);
    b.free(out);
}

/// One Gidney chunk, preserving the addend and carry-in and optionally
/// retaining the carry-out.  Every owned carry is measurement-uncomputed.
fn chunk_add(
    b: &mut B,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_in: Option<QubitId>,
    carry_out: Option<QubitId>,
) {
    let width = addend.len();
    assert_eq!(width, acc.len());
    if width == 0 {
        return;
    }
    let num_carries = if carry_out.is_some() {
        width
    } else {
        width - 1
    };
    if num_carries == 0 {
        if let Some(carry) = carry_in {
            b.cx(carry, acc[0]);
        }
        b.cx(addend[0], acc[0]);
        return;
    }

    let owned = num_carries - usize::from(carry_out.is_some());
    let mut carries = b.alloc_qubits(owned);
    if let Some(carry) = carry_out {
        carries.push(carry);
    }

    for i in 0..num_carries {
        let previous = if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        };
        if let Some(previous) = previous {
            b.cx(previous, addend[i]);
            b.cx(previous, acc[i]);
        }
        b.ccx(addend[i], acc[i], carries[i]);
        if let Some(previous) = previous {
            b.cx(previous, carries[i]);
        }
    }

    if carry_out.is_some() {
        let i = width - 1;
        let previous = if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        };
        if let Some(previous) = previous {
            b.cx(previous, addend[i]);
        }
        b.cx(addend[i], acc[i]);
    } else {
        b.cx(carries[num_carries - 1], acc[width - 1]);
        b.cx(addend[width - 1], acc[width - 1]);
    }

    for i in (0..owned).rev() {
        let previous = if i == 0 {
            carry_in
        } else {
            Some(carries[i - 1])
        };
        if let Some(previous) = previous {
            b.cx(previous, carries[i]);
        }
        let measured = b.alloc_bit();
        b.hmr(carries[i], measured);
        b.cz_if(addend[i], acc[i], measured);
        if let Some(previous) = previous {
            b.cx(previous, addend[i]);
        }
        b.cx(addend[i], acc[i]);
    }
    b.free_vec(&carries[..owned]);
}

fn chunk_bounds(width: usize, chunk: usize) -> Vec<(usize, usize)> {
    let chunks = width.div_ceil(chunk.max(1)).max(1);
    let (base, extra) = (width / chunks, width % chunks);
    let mut bounds = Vec::with_capacity(chunks);
    let mut lo = 0;
    for index in 0..chunks {
        let size = base + usize::from(index < extra);
        bounds.push((lo, lo + size));
        lo += size;
    }
    bounds
}

/// Exact value add with approximate measurement-only erasure of chunk carries.
///
/// Footprint discipline (the chunk ladder is the binding allocation at the
/// replay peak): the final carry-out is allocated only when the last chunk
/// starts, and each interior boundary carry is erased as soon as the chunk
/// that consumed it as carry-in has completed, so at most two boundary wires
/// are live at any time.
pub(crate) fn add_chunked_measured(
    b: &mut B,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_out: Option<QubitId>,
) {
    add_chunked_measured_with(b, addend, acc, carry_out, false);
}

/// Like [`add_chunked_measured`] but allocates the carry-out wire itself,
/// only when the last chunk starts, and returns it.
fn add_chunked_measured_late_carry(b: &mut B, addend: &[QubitId], acc: &[QubitId]) -> QubitId {
    add_chunked_measured_with(b, addend, acc, None, true).expect("late carry-out allocated")
}

fn add_chunked_measured_with(
    b: &mut B,
    addend: &[QubitId],
    acc: &[QubitId],
    carry_out: Option<QubitId>,
    late_carry_out: bool,
) -> Option<QubitId> {
    let bounds = chunk_bounds(addend.len(), replay_chunk());
    let legacy = std::env::var_os("SUB4_PP_LEGACY_CHUNK_ORDER").is_some();
    let erase = |b: &mut B, carry: QubitId, lo: usize, hi: usize| {
        let width = hi - lo;
        let compare = replay_chunk_compare().min(width);
        let phase = b.alloc_bit();
        b.hmr(carry, phase);
        cmp_lt_phase_conditioned(b, &acc[hi - compare..hi], &addend[hi - compare..hi], phase);
        b.free(carry);
    };
    let mut live_boundaries = Vec::<(QubitId, usize, usize)>::new();
    let mut carry_in: Option<QubitId> = None;
    let mut final_carry = carry_out;
    for (index, &(lo, hi)) in bounds.iter().enumerate() {
        let last = index + 1 == bounds.len();
        let next = if last {
            if final_carry.is_none() && late_carry_out {
                final_carry = Some(b.alloc_qubit());
            }
            final_carry
        } else {
            Some(b.alloc_qubit())
        };
        chunk_add(b, &addend[lo..hi], &acc[lo..hi], carry_in, next);
        if !legacy && index >= 1 {
            // carry_in (boundary index-1) has now been fully consumed by this
            // chunk, and the chunk below it is final: erase it immediately.
            let pos = live_boundaries
                .iter()
                .position(|&(q, _, _)| Some(q) == carry_in)
                .expect("consumed boundary is live");
            let (carry, plo, phi) = live_boundaries.remove(pos);
            erase(b, carry, plo, phi);
        }
        if !last {
            live_boundaries.push((next.expect("interior carry"), lo, hi));
        }
        carry_in = next;
    }

    for index in (0..live_boundaries.len()).rev() {
        let (carry, lo, hi) = live_boundaries[index];
        erase(b, carry, lo, hi);
    }
    final_carry
}

fn twos_complement_bits(value: U256, width: usize) -> Vec<bool> {
    let mut output = vec![false; width];
    let mut carry = true;
    for (i, bit_out) in output.iter_mut().enumerate() {
        let inverted = !value.bit(i);
        *bit_out = inverted ^ carry;
        carry &= inverted;
    }
    output
}

fn fused_operand_controls(
    f: U256,
    negative_f: &[bool],
    index: usize,
    plus_f: QubitId,
    plus_2f: QubitId,
    minus_f: QubitId,
) -> Vec<QubitId> {
    let mut controls = Vec::with_capacity(3);
    if f.bit(index) {
        controls.push(plus_f);
    }
    if index > 0 && f.bit(index - 1) {
        controls.push(plus_2f);
    }
    if negative_f[index] {
        controls.push(minus_f);
    }
    controls
}

/// Add the one-hot selected member of {-f,0,+f,+2f} without materialising a
/// 56-bit operand.  A single roving bit supplies the classical per-position
/// XOR of the three selectors.
fn fused_fold_maskfree(
    b: &mut B,
    acc: &[QubitId],
    f: U256,
    negative_f: &[bool],
    plus_f: QubitId,
    plus_2f: QubitId,
    minus_f: QubitId,
    first_carry: QubitId,
) {
    let width = acc.len();
    let controls = |index| fused_operand_controls(f, negative_f, index, plus_f, plus_2f, minus_f);

    for control in controls(0) {
        b.cx(control, acc[0]);
    }
    if width == 1 {
        return;
    }
    if width == 2 {
        b.cx(first_carry, acc[1]);
        for control in controls(1) {
            b.cx(control, acc[1]);
        }
        return;
    }

    let start = 1;
    let num_carries = width - 1 - start;
    let operand = b.alloc_qubit();
    let carries = b.alloc_qubits(num_carries);

    for offset in 0..num_carries {
        let i = start + offset;
        let previous = if offset == 0 {
            first_carry
        } else {
            carries[offset - 1]
        };
        let selectors = controls(i);
        if selectors.is_empty() {
            b.cx(previous, acc[i]);
            b.ccx(previous, acc[i], carries[offset]);
            b.cx(previous, carries[offset]);
        } else {
            for &control in &selectors {
                b.cx(control, operand);
            }
            b.cx(previous, operand);
            b.cx(previous, acc[i]);
            b.ccx(operand, acc[i], carries[offset]);
            b.cx(previous, carries[offset]);
            b.cx(previous, operand);
            for &control in &selectors {
                b.cx(control, operand);
            }
        }
    }

    b.cx(carries[num_carries - 1], acc[width - 1]);
    for control in controls(width - 1) {
        b.cx(control, acc[width - 1]);
    }

    for offset in (0..num_carries).rev() {
        let i = start + offset;
        let previous = if offset == 0 {
            first_carry
        } else {
            carries[offset - 1]
        };
        let selectors = controls(i);
        if selectors.is_empty() {
            b.cx(previous, carries[offset]);
            let measured = b.alloc_bit();
            b.hmr(carries[offset], measured);
            b.cz_if(previous, acc[i], measured);
        } else {
            for &control in &selectors {
                b.cx(control, operand);
            }
            b.cx(previous, carries[offset]);
            b.cx(previous, operand);
            let measured = b.alloc_bit();
            b.hmr(carries[offset], measured);
            b.cz_if(operand, acc[i], measured);
            b.cx(previous, operand);
            b.cx(operand, acc[i]);
            for &control in &selectors {
                b.cx(control, operand);
            }
        }
    }
    b.free_vec(&carries);
    b.free(operand);
}

fn signed_mod_add_pm_halve_fused(b: &mut B, sign: QubitId, source: &[QubitId], target: &[QubitId]) {
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    for &q in target {
        b.cx(sign, q);
    }
    let overflow = if std::env::var_os("SUB4_PP_LEGACY_CHUNK_ORDER").is_some() {
        let overflow = b.alloc_qubit();
        add_chunked_measured(b, source, target, Some(overflow));
        overflow
    } else {
        add_chunked_measured_late_carry(b, source, target)
    };

    let parity = b.alloc_qubit();
    b.cx(target[0], parity);

    b.x(sign);
    let not_sign_and_parity = and_clean(b, sign, parity);
    b.x(sign);
    let sign_and_parity = b.alloc_qubit();
    b.cx(parity, sign_and_parity);
    b.cx(not_sign_and_parity, sign_and_parity);
    b.x(overflow);
    let minus_f = and_clean(b, overflow, not_sign_and_parity);
    b.x(overflow);
    let plus_2f = and_clean(b, overflow, sign_and_parity);
    let plus_f = b.alloc_qubit();
    b.cx(minus_f, plus_f);
    b.cx(sign, plus_f);
    b.cx(parity, plus_f);

    let negative_f = twos_complement_bits(f, replay_fold_window());
    fused_fold_maskfree(
        b,
        &target[..replay_fold_window()],
        f,
        &negative_f,
        plus_f,
        plus_2f,
        minus_f,
        not_sign_and_parity,
    );

    b.cx(minus_f, plus_f);
    b.cx(sign, plus_f);
    b.cx(parity, plus_f);
    b.free(plus_f);
    and_uncompute(b, plus_2f, overflow, sign_and_parity);
    b.x(overflow);
    and_uncompute(b, minus_f, overflow, not_sign_and_parity);
    b.x(overflow);
    b.cx(parity, sign_and_parity);
    b.cx(not_sign_and_parity, sign_and_parity);
    b.free(sign_and_parity);
    b.x(sign);
    and_uncompute(b, not_sign_and_parity, sign, parity);
    b.x(sign);

    b.cx(overflow, parity);
    b.cx(sign, parity);
    let phase = b.alloc_bit();
    b.hmr(overflow, phase);
    cmp_lt_phase_conditioned(
        b,
        &target[N - replay_flag_compare()..],
        &source[N - replay_flag_compare()..],
        phase,
    );
    b.free(overflow);

    for &q in target {
        b.cx(sign, q);
    }
    for i in 0..N - 1 {
        b.swap(target[i], target[i + 1]);
    }
    b.cx(parity, target[N - 1]);
    b.cx(target[N - 1], parity);
    b.free(parity);
}

/// Dormant fused inverse-replay cell.  `sign=0` adds `source` and `sign=1`
/// subtracts it, so this emits
///
///     target <- 2*target + (-1)^sign*source (mod p)
///
/// with one pseudo-Mersenne correction ripple instead of the separate
/// doubling and signed-add correction ripples.
fn signed_mod_double_add_pm_fused(
    b: &mut B,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
) {
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));

    let doubled_out = b.alloc_qubit();
    b.swap(target[N - 1], doubled_out);
    for i in (0..N - 1).rev() {
        b.swap(target[i], target[i + 1]);
    }

    for &q in target {
        b.cx(sign, q);
    }
    let add_out = if std::env::var_os("SUB4_PP_LEGACY_CHUNK_ORDER").is_some() {
        let add_out = b.alloc_qubit();
        add_chunked_measured(b, source, target, Some(add_out));
        add_out
    } else {
        add_chunked_measured_late_carry(b, source, target)
    };

    // In the complemented subtraction frame the correction multiple is
    // d+o when sign=0 and o-d when sign=1, hence {-1,0,+1,+2}.
    let sign_xor_add = b.alloc_qubit();
    b.cx(sign, sign_xor_add);
    b.cx(add_out, sign_xor_add);
    let routed = and_clean(b, doubled_out, sign_xor_add);
    let minus_f = and_clean(b, routed, sign);
    let plus_2f = b.alloc_qubit();
    b.cx(routed, plus_2f);
    b.cx(minus_f, plus_2f);
    let plus_f = b.alloc_qubit();
    b.cx(doubled_out, plus_f);
    b.cx(add_out, plus_f);
    b.cx(minus_f, plus_f);

    // +/-f is odd and +2f is even, so d^o selects the only bit-0 carry.
    let odd_correction = b.alloc_qubit();
    b.cx(doubled_out, odd_correction);
    b.cx(add_out, odd_correction);
    let first_carry = and_clean(b, target[0], odd_correction);
    let negative_f = twos_complement_bits(f, replay_fold_window());
    fused_fold_maskfree(
        b,
        &target[..replay_fold_window()],
        f,
        &negative_f,
        plus_f,
        plus_2f,
        minus_f,
        first_carry,
    );

    b.cx(odd_correction, target[0]);
    and_uncompute(b, first_carry, target[0], odd_correction);
    b.cx(odd_correction, target[0]);
    b.cx(doubled_out, odd_correction);
    b.cx(add_out, odd_correction);
    b.free(odd_correction);

    b.cx(doubled_out, plus_f);
    b.cx(add_out, plus_f);
    b.cx(minus_f, plus_f);
    b.free(plus_f);
    b.cx(minus_f, plus_2f);
    b.cx(routed, plus_2f);
    b.free(plus_2f);
    and_uncompute(b, minus_f, routed, sign);
    and_uncompute(b, routed, doubled_out, sign_xor_add);
    b.cx(add_out, sign_xor_add);
    b.cx(sign, sign_xor_add);
    b.free(sign_xor_add);

    // After the fold, still in the complemented frame,
    // target[0] = sign ^ source[0] ^ d ^ o.  Clear d without a second ripple.
    b.cx(target[0], doubled_out);
    b.cx(sign, doubled_out);
    b.cx(source[0], doubled_out);
    b.cx(add_out, doubled_out);
    b.free(doubled_out);

    let phase = b.alloc_bit();
    b.hmr(add_out, phase);
    cmp_lt_phase_conditioned(
        b,
        &target[N - replay_flag_compare()..],
        &source[N - replay_flag_compare()..],
        phase,
    );
    b.free(add_out);
    for &q in target {
        b.cx(sign, q);
    }
}

fn signed_mod_add_pm(b: &mut B, sign: QubitId, source: &[QubitId], target: &[QubitId]) {
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    for &q in target {
        b.cx(sign, q);
    }
    let overflow = b.alloc_qubit();
    add_chunked_measured(b, source, target, Some(overflow));
    cadd_nbit_const_direct_trunc_fast(
        b,
        replay_fold_target(target),
        f,
        overflow,
        endpoint_fold_window(),
    );
    let phase = b.alloc_bit();
    b.hmr(overflow, phase);
    cmp_lt_phase_conditioned(
        b,
        &target[N - replay_flag_compare()..],
        &source[N - replay_flag_compare()..],
        phase,
    );
    b.free(overflow);
    for &q in target {
        b.cx(sign, q);
    }
}

fn mod_halve_pm(b: &mut B, target: &[QubitId]) {
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let parity = b.alloc_qubit();
    b.cx(target[0], parity);
    csub_nbit_const_direct_trunc_fast(
        b,
        replay_fold_target(target),
        f,
        parity,
        endpoint_fold_window(),
    );
    for i in 0..N - 1 {
        b.swap(target[i], target[i + 1]);
    }
    b.cx(parity, target[N - 1]);
    b.cx(target[N - 1], parity);
    b.free(parity);
}

fn mod_double_pm(b: &mut B, target: &[QubitId]) {
    let f = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    let overflow = b.alloc_qubit();
    b.swap(target[N - 1], overflow);
    for i in (0..N - 1).rev() {
        b.swap(target[i], target[i + 1]);
    }
    cadd_nbit_const_direct_trunc_fast(
        b,
        replay_fold_target(target),
        f,
        overflow,
        endpoint_fold_window(),
    );
    b.cx(target[0], overflow);
    b.free(overflow);
}

fn seed_round_one(b: &mut B, sign: QubitId, source: &[QubitId], target: &[QubitId]) {
    for i in 0..N {
        b.cx(source[i], target[i]);
        b.cx(sign, target[i]);
    }
    let f_minus_one = U256::MAX.wrapping_sub(SECP256K1_P);
    csub_nbit_const_direct_trunc_fast(b, target, f_minus_one, sign, 32);
}

fn seed_round_one_inverse(b: &mut B, sign: QubitId, source: &[QubitId], target: &[QubitId]) {
    let f_minus_one = U256::MAX.wrapping_sub(SECP256K1_P);
    cadd_nbit_const_direct_trunc_fast(b, target, f_minus_one, sign, 32);
    for i in (0..N).rev() {
        b.cx(sign, target[i]);
        b.cx(source[i], target[i]);
    }
}

fn replay_halving(b: &mut B, tape: &[QubitId], x: &[QubitId], y: &[QubitId]) {
    for (round, &sign) in tape.iter().enumerate() {
        let (source, target) = if round.is_multiple_of(2) {
            (x, y)
        } else {
            (y, x)
        };
        if round == 0 {
            mod_halve_pm(b, target);
        } else if round == 1 {
            seed_round_one(b, sign, source, target);
            mod_halve_pm(b, target);
        } else {
            signed_mod_add_pm_halve_fused(b, sign, source, target);
        }
    }
}

fn replay_doubling_inverse(b: &mut B, tape: &[QubitId], x: &[QubitId], y: &[QubitId]) {
    let fused = std::env::var_os("SUB4_PINGPONG_UNFUSED_INVERSE").is_none();
    for round in (0..tape.len()).rev() {
        let sign = tape[round];
        let (source, target) = if round.is_multiple_of(2) {
            (x, y)
        } else {
            (y, x)
        };
        if fused && round > 1 {
            b.x(sign);
            signed_mod_double_add_pm_fused(b, sign, source, target);
            b.x(sign);
        } else {
            mod_double_pm(b, target);
        }
        if round == 1 {
            seed_round_one_inverse(b, sign, source, target);
        } else if round > 1 && !fused {
            b.x(sign);
            signed_mod_add_pm(b, sign, source, target);
            b.x(sign);
        }
    }
}

/// Full four-register affine point-add candidate using the existing
/// TrailMix coordinate shell and symmetric in-place square verbatim.  Only
/// the two division callbacks differ from the baseline construction.
pub(crate) fn build_pingpong_point_add() -> Vec<Op> {
    if mux_round0_correction_enabled() {
        set_default_env("DIALOG_GCD_FOLD_MAJ1", "1");
    }
    trailmix_ludicrous::load_schedule();
    let mut circ = B::new();
    let x = circ.alloc_qubits(N);
    let y = circ.alloc_qubits(N);
    let ox = circ.alloc_bits(N);
    let oy = circ.alloc_bits(N);

    let original_x_wires = x.clone();
    let mut working_x = x;
    trailmix_ludicrous::ec_add::ec_add_with_division(
        &mut circ,
        &mut working_x,
        &y,
        &ox,
        &oy,
        |circ, denominator, numerator, inverse| {
            pingpong_mod_mul_div_in_place(
                circ,
                &denominator,
                numerator,
                if inverse {
                    PingPongDirection::Divide
                } else {
                    PingPongDirection::Multiply
                },
            );
            denominator
        },
    );

    // The ping-pong component restores the caller's exact wire identities,
    // so unlike constructions that return a routed register no tail swaps are
    // necessary (or permitted to hide here).
    assert_eq!(working_x, original_x_wires);
    circ.declare_qubit_register(&original_x_wires);
    circ.declare_qubit_register(&y);
    circ.declare_bit_register(&ox);
    circ.declare_bit_register(&oy);
    circ.b0_finalize();
    let ops = circ.take_ops();
    if pp_profile::enabled() {
        pp_profile::report(
            &ops,
            &circ.phase_transitions,
            circ.peak_qubits,
            circ.peak_ops_idx,
            circ.peak_phase,
            &circ.active_timeline,
        );
    }
    ops
}

/// One bit-parallel batch through the complete affine-add candidate.  This is
/// deliberately separate from the 9,024-shot challenge runner: it gates the
/// composition and reports its raw resource shape before nonce work begins.
#[allow(dead_code)]
pub(crate) fn pingpong_point_add_simulator_selfcheck() {
    use sha3::{
        digest::{ExtendableOutput, Update, XofReader},
        Shake256,
    };

    let ops = build_pingpong_point_add();
    let (num_qubits, num_bits, num_registers, registers) = analyze_ops(ops.iter());
    assert_eq!(num_registers, 4);
    assert_eq!(registers.len(), 4);
    assert!(registers.iter().all(|register| register.len() == N));
    assert!(registers[0]
        .iter()
        .chain(&registers[1])
        .all(|wire| matches!(wire, QubitOrBit::Qubit(_))));
    assert!(registers[2]
        .iter()
        .chain(&registers[3])
        .all(|wire| matches!(wire, QubitOrBit::Bit(_))));

    let curve = WeierstrassEllipticCurve {
        modulus: SECP256K1_P,
        a: U256::ZERO,
        b: U256::from(7),
        gx: U256::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("valid generator x"),
        gy: U256::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .expect("valid generator y"),
        order: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .expect("valid group order"),
    };

    let mut input_seed = Shake256::default();
    input_seed.update(b"pingpong full affine point-add composition gate");
    let mut input_reader = input_seed.finalize_xof();
    let mut targets = Vec::with_capacity(64);
    let mut offsets = Vec::with_capacity(64);
    let mut expected = Vec::with_capacity(64);
    while targets.len() < 64 {
        let mut scalar_bytes = [[0u8; 32]; 2];
        XofReader::read(&mut input_reader, &mut scalar_bytes[0]);
        XofReader::read(&mut input_reader, &mut scalar_bytes[1]);
        let target = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(scalar_bytes[0]));
        let offset = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(scalar_bytes[1]));
        if target.0 == offset.0
            || (target.0.is_zero() && target.1.is_zero())
            || (offset.0.is_zero() && offset.1.is_zero())
        {
            continue;
        }
        expected.push(curve.add(target.0, target.1, offset.0, offset.1));
        targets.push(target);
        offsets.push(offset);
    }

    let mut simulator_seed = Shake256::default();
    simulator_seed.update(b"pingpong full affine point-add simulator randomness");
    let mut simulator_reader = simulator_seed.finalize_xof();
    let mut sim = Simulator::new(
        num_qubits as usize,
        num_bits as usize,
        &mut simulator_reader,
    );
    for shot in 0..64 {
        sim.set_register(&registers[0], targets[shot].0, shot);
        sim.set_register(&registers[1], targets[shot].1, shot);
        sim.set_register(&registers[2], offsets[shot].0, shot);
        sim.set_register(&registers[3], offsets[shot].1, shot);
    }
    sim.apply_iter(ops.iter());

    for shot in 0..64 {
        assert_eq!(sim.get_register(&registers[0], shot), expected[shot].0);
        assert_eq!(sim.get_register(&registers[1], shot), expected[shot].1);
        assert_eq!(sim.get_register(&registers[2], shot), offsets[shot].0);
        assert_eq!(sim.get_register(&registers[3], shot), offsets[shot].1);
    }
    assert_eq!(sim.phase, 0, "phase garbage in full ping-pong point add");

    for register in &registers {
        for wire in register {
            if let QubitOrBit::Qubit(q) = *wire {
                *sim.qubit_mut(q) = 0;
            }
        }
    }
    for q in 0..num_qubits {
        assert_eq!(
            sim.qubit(QubitId(q)),
            0,
            "dirty ancilla q{q} in full ping-pong point add"
        );
    }

    let emitted_toffoli = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();
    let average_executed = sim.stats.toffoli_gates as f64 / 64.0;
    eprintln!(
        "pingpong full affine add: {emitted_toffoli} emitted / {average_executed:.3} executed Toffoli, {num_qubits} qubits"
    );
}

/// Full 64-lane target-simulator diagnostic for both public directions.
/// Kept callable because the repository-wide `cargo test` target contains
/// unrelated stale tests; this component can still be gated in isolation.
#[allow(dead_code)]
pub(crate) fn pingpong_simulator_selfcheck() {
    use crate::circuit::QubitOrBit;
    use sha3::{
        digest::{ExtendableOutput, Update},
        Shake256,
    };

    assert_eq!(value_width(0), VALUE_WIDTH);
    assert!(value_width(rounds() - 1) >= 8);
    assert!((1..rounds()).all(|i| value_width(i) <= value_width(i - 1)));

    let mut state = 0x3141_5926_5358_9793u64;
    let mut denominators = Vec::with_capacity(64);
    for shot in 0..64 {
        let mut limbs = [0u64; 4];
        for limb in &mut limbs {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *limb = state;
        }
        let mut d = U256::from_limbs(limbs) % SECP256K1_P;
        if d.is_zero() {
            d = U256::from(1);
        }
        let want_odd = shot % 2 == 0;
        if d.bit(0) != want_odd {
            d = if want_odd {
                d.wrapping_add(U256::from(1))
            } else {
                d.wrapping_sub(U256::from(1))
            };
        }
        denominators.push(d);
    }
    let numerators: Vec<U256> = denominators
        .iter()
        .map(|&d| {
            d.mul_mod(U256::from(17), SECP256K1_P)
                .add_mod(U256::from(5), SECP256K1_P)
        })
        .collect();
    let fold = U256::MAX
        .wrapping_sub(SECP256K1_P)
        .wrapping_add(U256::from(1));
    assert!(numerators.iter().all(|&c| c >= fold));

    {
        let mut b = B::new();
        let sign = b.alloc_qubit();
        let source = b.alloc_qubits(N);
        let target = b.alloc_qubits(N);
        signed_mod_add_pm(&mut b, sign, &source, &target);
        let num_qubits = b.next_qubit as usize;
        let num_bits = b.next_bit as usize;
        let ops = b.take_ops();
        let mut shake = Shake256::default();
        shake.update(b"pingpong approximate signed modular add test");
        let mut reader = shake.finalize_xof();
        let mut sim = Simulator::new(num_qubits, num_bits, &mut reader);
        let source_reg: Vec<QubitOrBit> = source.iter().copied().map(QubitOrBit::Qubit).collect();
        let target_reg: Vec<QubitOrBit> = target.iter().copied().map(QubitOrBit::Qubit).collect();
        for shot in 0..64 {
            sim.set_register(&source_reg, denominators[shot], shot);
            sim.set_register(&target_reg, numerators[shot], shot);
            if shot % 2 == 1 {
                *sim.qubit_mut(sign) |= 1 << shot;
            }
        }
        sim.apply_iter(ops.iter());
        for shot in 0..64 {
            let source_value = denominators[shot];
            let target_value = numerators[shot];
            let expected = if shot % 2 == 1 {
                if target_value >= source_value {
                    target_value - source_value
                } else {
                    SECP256K1_P - (source_value - target_value)
                }
            } else {
                target_value.add_mod(source_value, SECP256K1_P)
            };
            assert_eq!(sim.get_register(&source_reg, shot), source_value);
            assert_eq!(sim.get_register(&target_reg, shot), expected);
        }
        assert_eq!(sim.phase, 0, "phase garbage in signed modular add");
    }

    {
        let mut b = B::new();
        let mut u = b.alloc_qubits(VALUE_WIDTH);
        let mut v = b.alloc_qubits(VALUE_WIDTH);
        let input_u = u.clone();
        let input_v = v.clone();
        let _tape = value_walk(&mut b, &mut u, &mut v, rounds());
        let nq = b.next_qubit as usize;
        let nb = b.next_bit as usize;
        let ops = b.take_ops();
        let mut shake = Shake256::default();
        shake.update(b"pingpong value walk test");
        let mut reader = shake.finalize_xof();
        let mut sim = Simulator::new(nq, nb, &mut reader);
        let input_u_reg: Vec<QubitOrBit> = input_u[..N]
            .iter()
            .copied()
            .map(QubitOrBit::Qubit)
            .collect();
        let input_v_reg: Vec<QubitOrBit> = input_v[..N]
            .iter()
            .copied()
            .map(QubitOrBit::Qubit)
            .collect();
        let terminal_u: Vec<QubitOrBit> = u.iter().copied().map(QubitOrBit::Qubit).collect();
        let terminal_v: Vec<QubitOrBit> = v.iter().copied().map(QubitOrBit::Qubit).collect();
        for shot in 0..64 {
            sim.set_register(&input_u_reg, SECP256K1_P, shot);
            sim.set_register(&input_v_reg, denominators[0], shot);
        }
        sim.apply_iter(ops.iter());
        for shot in 0..64 {
            assert_eq!(sim.get_register(&terminal_u, shot), U256::from(255));
            assert_eq!(sim.get_register(&terminal_v, shot), U256::from(255));
        }
        assert_eq!(sim.phase, 0);
    }

    for direction in [PingPongDirection::Divide, PingPongDirection::Multiply] {
        let mut b = B::new();
        let denominator = b.alloc_qubits(N);
        let numerator = b.alloc_qubits(N);
        let live_inputs = b.active_qubits;
        pingpong_mod_mul_div_in_place(&mut b, &denominator, &numerator, direction);
        assert_eq!(b.active_qubits, live_inputs);

        let num_qubits = b.next_qubit as usize;
        let num_bits = b.next_bit as usize;
        let peak_qubits = b.peak_qubits;
        let ops = b.take_ops();
        let emitted_toffoli = ops
            .iter()
            .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
            .count();
        let mut condition_depth = 0i32;
        let mut executed_toffoli = 0.0f64;
        for op in &ops {
            match op.kind {
                OperationType::PushCondition => condition_depth += 1,
                OperationType::PopCondition => condition_depth -= 1,
                OperationType::CCX | OperationType::CCZ => {
                    executed_toffoli += 0.5f64.powi(condition_depth)
                }
                _ => {}
            }
        }
        assert!(emitted_toffoli > 0);
        assert_eq!(condition_depth, 0);
        eprintln!(
            "pingpong {direction:?}: {emitted_toffoli} emitted / {executed_toffoli:.1} executed Toffoli, {peak_qubits} peak qubits"
        );

        let mut shake = Shake256::default();
        shake.update(b"pingpong production component test");
        let mut reader = shake.finalize_xof();
        let mut sim = Simulator::new(num_qubits, num_bits, &mut reader);
        let denominator_reg: Vec<QubitOrBit> =
            denominator.iter().copied().map(QubitOrBit::Qubit).collect();
        let numerator_reg: Vec<QubitOrBit> =
            numerator.iter().copied().map(QubitOrBit::Qubit).collect();

        for shot in 0..64 {
            let d = denominators[shot];
            let c = numerators[shot];
            sim.set_register(&denominator_reg, d, shot);
            sim.set_register(&numerator_reg, c, shot);
        }
        sim.apply_iter(ops.iter());

        for shot in 0..64 {
            let d = denominators[shot];
            let c = numerators[shot];
            let expected = match direction {
                PingPongDirection::Divide => c.mul_mod(
                    d.inv_mod(SECP256K1_P).expect("nonzero denominator"),
                    SECP256K1_P,
                ),
                PingPongDirection::Multiply => c.mul_mod(d, SECP256K1_P),
            };
            assert_eq!(sim.get_register(&denominator_reg, shot), d);
            assert_eq!(
                sim.get_register(&numerator_reg, shot),
                expected,
                "numerator mismatch in {direction:?}, shot {shot}, d={d:#x}, c={c:#x}"
            );
        }
        assert_eq!(sim.phase, 0, "phase garbage in {direction:?}");
        for q in 0..num_qubits as u64 {
            let q = QubitId(q);
            if denominator.contains(&q) || numerator.contains(&q) {
                continue;
            }
            assert_eq!(sim.qubit(q), 0, "dirty ancilla {q:?} in {direction:?}");
        }
    }
}

#[cfg(test)]
#[test]
fn divide_and_multiply_preserve_the_abi_and_clean_ancillas() {
    pingpong_simulator_selfcheck();
}
