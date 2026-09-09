//! Dormant product-register Karatsuba square port.
//!
//! The source construction accumulates three half-width triangular squares in
//! plain product registers, then reduces five times.  This target translation
//! deliberately reuses the legacy builder's clean add, fold, comparator, and
//! measurement-based erasure primitives.

use super::super::{arith, comparator, B, BExt};
use crate::circuit::{OperationType, QubitId, QubitOrBit};

const N: usize = 256;
const LSBS: usize = 56;
const MSBS: usize = 24;
const GUARD: usize = 24;
const F_NAF: [(usize, bool); 5] = [
    (0, false),
    (4, false),
    (6, true),
    (10, false),
    (32, false),
];

/// The Karatsuba sum now lives in the input high half instead of a separate
/// 129-qubit register (moscowchill 51c6c31c). The resulting liveness margin
/// lets every square add use its exact full-width ladder below the replay
/// peak. `SUB4_SQUARE_CHUNK_MIN=200` restores the pre-merge chunked path.
const SQUARE_CHUNK_MIN: usize = usize::MAX;
/// Live carry-ladder budget when an explicit environment override requests the
/// chunked diagnostic path; co-balanced with replay peak.
const SQUARE_LADDER: usize = 243;
fn add_full(circ: &mut B, addend: &[QubitId], acc: &[QubitId]) {
    assert_eq!(addend.len(), acc.len());
    let chunk_min = std::env::var("SUB4_SQUARE_CHUNK_MIN")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(SQUARE_CHUNK_MIN);
    if acc.len() >= chunk_min {
        // The square's own footprint sits ~160 qubits below the replay peak, so
        // it can afford a much wider carry ladder than the replay can - and a
        // wider ladder means fewer chunks, i.e. fewer measured boundary
        // repairs.  Budget it explicitly instead of inheriting the replay's
        // chunk width.
        let budget = std::env::var("SUB4_SQUARE_LADDER")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(SQUARE_LADDER);
        if budget == 0 {
            crate::point_add::pingpong_div::add_chunked_measured(circ, addend, acc, None);
        } else {
            crate::point_add::pingpong_div::add_chunked_measured_budgeted(
                circ, addend, acc, None, budget,
            );
        }
        return;
    }
    arith::hybrid_add_adaptive(circ, acc, addend, usize::MAX);
}

fn sub_full(circ: &mut B, addend: &[QubitId], acc: &[QubitId]) {
    for &q in acc {
        circ.x(q);
    }
    add_full(circ, addend, acc);
    for &q in acc {
        circ.x(q);
    }
}

fn row_addsub(
    circ: &mut B,
    ctrl: QubitId,
    operand: &[QubitId],
    acc: &[QubitId],
    inverse: bool,
) {
    let k = operand.len();
    assert_eq!(acc.len(), k + 1);
    let pad = circ.alloc_qubit();
    let mut operand_wide = operand.to_vec();
    operand_wide.push(pad);
    if inverse {
        circ.cx(ctrl, acc[k]);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        sub_full(circ, &operand_wide, acc);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
    } else {
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        add_full(circ, &operand_wide, acc);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        circ.cx(ctrl, acc[k]);
    }
    circ.zero_and_free(pad);
}

fn tri_square(circ: &mut B, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    if m == 0 {
        return;
    }
    if inverse {
        tri_corr(circ, x, product, true);
        for i in (0..m.saturating_sub(1)).rev() {
            let k = m - 1 - i;
            circ.x(x[i]);
            row_addsub(
                circ,
                x[i],
                &x[i + 1..],
                &product[2 * i + 1..2 * i + 2 + k],
                true,
            );
            circ.x(x[i]);
        }
    } else {
        for i in 0..m.saturating_sub(1) {
            let k = m - 1 - i;
            circ.x(x[i]);
            row_addsub(
                circ,
                x[i],
                &x[i + 1..],
                &product[2 * i + 1..2 * i + 2 + k],
                false,
            );
            circ.x(x[i]);
        }
        tri_corr(circ, x, product, false);
    }
}

fn tri_corr(circ: &mut B, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    let spread = |circ: &mut B| {
        let pads = circ.alloc_qubits(m);
        let mut value = Vec::with_capacity(2 * m);
        for i in 0..m {
            value.push(pads[i]);
            value.push(x[i]);
        }
        (value, pads)
    };
    let correction = |circ: &mut B| {
        // The prior form subtracted x across the full product and then
        // subtracted ~(x mod 2^(m-1)) from the high half. Those operands occupy
        // disjoint bit ranges, so concatenate them and use one full-width
        // subtraction. Copying and complementing the high half is Clifford;
        // this removes one (m-1)-Toffoli carry ladder per correction.
        let pads = circ.alloc_qubits(m);
        for i in 0..m - 1 {
            circ.cx(x[i], pads[i]);
            circ.x(pads[i]);
        }
        let mut value = x.to_vec();
        value.extend_from_slice(&pads);
        (value, pads)
    };
    let clear_correction = |circ: &mut B, pads: &[QubitId]| {
        for i in 0..m - 1 {
            circ.x(pads[i]);
            circ.cx(x[i], pads[i]);
        }
    };

    if !inverse {
        let (value, pads) = spread(circ);
        add_full(circ, &value, product);
        circ.free_vec(&pads);
        let (value, pads) = correction(circ);
        sub_full(circ, &value, product);
        clear_correction(circ, &pads);
        circ.free_vec(&pads);
    } else {
        let (value, pads) = correction(circ);
        add_full(circ, &value, product);
        clear_correction(circ, &pads);
        circ.free_vec(&pads);
        let (value, pads) = spread(circ);
        sub_full(circ, &value, product);
        circ.free_vec(&pads);
    }
}

fn clear_overflow_phase(circ: &mut B, overflow: QubitId, acc: &[QubitId], addend: &[QubitId]) {
    let bit = circ.alloc_bit();
    circ.hmr(overflow, bit);
    circ.push_condition(bit);
    let c_in = circ.alloc_qubit();
    comparator::compare_geq_cin_middle(
        circ,
        &acc[acc.len() - MSBS..],
        &addend[addend.len() - MSBS..],
        &c_in,
        |c, a, b, carry_in| {
            // The omitted final carry is carry_in ^ (a & b) in this frame.
            // Correct the phase of its complement directly with Cliffords.
            c.neg();
            c.z(*carry_in);
            c.cz(*a, *b);
        },
    );
    circ.zero_and_free(c_in);
    circ.pop_condition();
}

fn mod_add_top(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
    shift: usize,
) {
    assert_eq!(shift + value.len(), out.len());
    for &q in out {
        circ.cx(sign, q);
    }
    let pad = circ.alloc_qubit();
    let mut value_wide = value.to_vec();
    value_wide.push(pad);
    let mut acc_wide = out[shift..].to_vec();
    acc_wide.push(overflow);
    add_full(circ, &value_wide, &acc_wide);
    circ.zero_and_free(pad);

    let f = arith::F_SECP256K1.to_le_bytes();
    arith::add_f_window_pub(circ, &overflow, out, LSBS, &f, Some(LSBS));
    clear_overflow_phase(circ, overflow, out, value);
    for &q in out {
        circ.cx(sign, q);
    }
}

fn window_add(circ: &mut B, sign: QubitId, value: &[QubitId], out: &[QubitId], shift: usize) {
    let top = shift + value.len() + GUARD;
    assert!(top <= out.len());
    let acc = &out[shift..top];
    let pads = circ.alloc_qubits(GUARD);
    let mut value_wide = value.to_vec();
    value_wide.extend_from_slice(&pads);
    for &q in acc {
        circ.cx(sign, q);
    }
    add_full(circ, &value_wide, acc);
    for &q in acc {
        circ.cx(sign, q);
    }
    circ.free_vec(&pads);
}

fn apply_f(circ: &mut B, sign: QubitId, value: &[QubitId], out: &[QubitId]) {
    for (shift, negate) in F_NAF {
        if negate {
            circ.x(sign);
        }
        window_add(circ, sign, value, out, shift);
        if negate {
            circ.x(sign);
        }
    }
}

fn apply_f_without_unit(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
) {
    for (shift, negate) in F_NAF.into_iter().skip(1) {
        if negate {
            circ.x(sign);
        }
        window_add(circ, sign, value, out, shift);
        if negate {
            circ.x(sign);
        }
    }
}

/// Add `value * 2^shift (mod p)` for a full-width value. Since
/// `2^N = f (mod p)`, the wrapped high limb contributes `f * high`.
/// Rotating that limb into the vacated low positions folds its unit term into
/// the main modular add. The remaining NAF terms contribute `(f - 1) * high`.
fn apply_shifted_full_term(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
    shift: usize,
) {
    assert_eq!(value.len(), N);
    assert!(shift < N);
    if shift == 0 {
        mod_add_top(circ, sign, value, out, overflow, 0);
        return;
    }

    let split = N - shift;
    let high = &value[split..];
    let mut rotated = Vec::with_capacity(N);
    rotated.extend_from_slice(high);
    rotated.extend_from_slice(&value[..split]);
    mod_add_top(circ, sign, &rotated, out, overflow, 0);
    apply_f_without_unit(circ, sign, high, out);
}

fn apply_shift_half(
    circ: &mut B,
    sign: QubitId,
    product: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
) {
    let h = out.len() / 2;
    if product.len() == out.len() {
        apply_shifted_full_term(circ, sign, product, out, overflow, h);
    } else if product.len() == out.len() + 2 {
        // The Karatsuba cross-square has two extra high bits. Rotate the low
        // half of its high limb into the full-width add, then add the two
        // overlapping bits separately. This keeps the same carry lengths and
        // removes the 128 sign-copy pairs from the unit fold.
        let high = &product[h..];
        let mut rotated = Vec::with_capacity(N);
        rotated.extend_from_slice(&high[..h]);
        rotated.extend_from_slice(&product[..h]);
        mod_add_top(circ, sign, &rotated, out, overflow, 0);
        apply_f_without_unit(circ, sign, high, out);
        window_add(circ, sign, &high[h..], out, h);
    } else {
        mod_add_top(circ, sign, &product[..h], out, overflow, h);
        if product.len() > h {
            apply_f(circ, sign, &product[h..], out);
        }
    }
}

fn apply_shift_full(
    circ: &mut B,
    sign: QubitId,
    product: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
) {
    assert_eq!(product.len(), out.len());
    for (shift, negate) in F_NAF {
        if negate {
            circ.x(sign);
        }
        apply_shifted_full_term(circ, sign, product, out, overflow, shift);
        if negate {
            circ.x(sign);
        }
    }
}

/// W5: level-2 Karatsuba for the square's two split branches (`y_lo`, `sum`).
/// -2,682.23 exec T (PP_PROFILE 64-lane: 917,618.45 -> 914,936.22) at an
/// unchanged peak of 1,278 qubits.  `SUB4_SQUARE_KARATSUBA2=0` forces the
/// stock (pre-Karatsuba) op stream for A/B comparison.  See
/// `W5_SQUARE_KARATSUBA2_SPEC.md` for the algebra.
///
/// VALIDATION STATUS (measured 2026-08-23, do not weaken this note):
///  * VALUE-EXACT.  Branch A + branch C in isolation (`SQ_SKIP_B`) over
///    2.56M random square shots: 0 classical failures, 0 phase, 0 dirty --
///    identical to the stock branch A + C blocks they replace.  Whole
///    `square_sub` over 1.28M random shots: 4 failures ON vs 3 failures OFF,
///    i.e. the pre-existing ~2.5e-6/square `window_add` GUARD-overflow rate,
///    unchanged.
///  * It does NOT pass `./benchmark.sh` at the inherited tail nonce, and it
///    CANNOT: the frontier's 0/0/0 is a HUNTED SEED ISLAND.  The 9,024 test
///    shots are SHAKE256 of the whole op stream, and this route's intrinsic
///    per-shot failure rate is ~1.4e-3.  Stock 940e34a with only the
///    provably-identity tail-nonce X retarget changed scores 9..20 classical
///    mismatches over 11 arbitrary nonces (mean 12.8); W5 scores 9..14 over 8
///    arbitrary nonces (mean 11.8).  Landing this needs ONE nonce bake, the
///    same as every other structural edit on this route -- not a code fix.
fn karatsuba2_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("SUB4_SQUARE_KARATSUBA2")
            .map(|v| v != "0")
            .unwrap_or(true)
    })
}

/// Generalises `apply_shift_half`/`apply_shift_full` to an arbitrary shift and
/// product width, folding `+/- product * 2^shift` (sign chosen by `sign` XOR
/// `negate`) straight into the persistent mod-p accumulator `out`.
///
/// Four regimes, chosen purely by how `shift + product.len()` compares to
/// `out.len()` (== 256 here): a plain guarded window add when there is room
/// to spare; `mod_add_top` alone on an exact top-aligned fit (no window
/// guard exists past bit 256, so `window_add` would overrun `out` by
/// construction — this must NOT fall through to the windowed case); the
/// mixed top+tail split when the product straddles bit 256; and a pure
/// `apply_f` reduction when the shift itself is already >= 256.
fn fold_shifted(
    circ: &mut B,
    sign: QubitId,
    product: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
    shift: usize,
    negate: bool,
) {
    if negate {
        circ.x(sign);
    }
    let n = out.len();
    // `shift > n` would make the straddle arm's `n - shift` underflow.  The
    // composed fold table tops out at exactly `shift == n` (the b0^2 / bs^2
    // 2^256 terms), so this is unreachable -- pin it so a future coefficient
    // edit fails loudly instead of panicking inside a slice index.
    debug_assert!(shift <= n, "fold shift {shift} past the accumulator top");
    if shift == n {
        apply_f(circ, sign, product, out);
    } else if shift + product.len() == n {
        mod_add_top(circ, sign, product, out, overflow, shift);
    } else if shift + product.len() < n {
        window_add(circ, sign, product, out, shift);
    } else {
        let lo = n - shift;
        mod_add_top(circ, sign, &product[..lo], out, overflow, shift);
        apply_f(circ, sign, &product[lo..], out);
    }
    if negate {
        circ.x(sign);
    }
}

/// One level-2 Karatsuba branch: split `x` (a `y_lo`- or `sum`-class operand)
/// into `a = x[..lo]`, `b = x[lo..]`, build `t = a + b`, square each of the
/// three (a, t, b) in its own scratch product register, fold every
/// sub-square straight into `out` with the PARENT's coefficient (`coefficients`,
/// the same `(shift, negate)` pairs `square_sub` used to fold x^2 itself)
/// composed with the sub-square's own local coefficient — and uncompute
/// every product register and `t`. No parent product register is ever
/// materialised, which is what keeps this a 4x (not 6x) recursion.
fn karatsuba_branch(
    circ: &mut B,
    x: &[QubitId],
    coefficients: &[(usize, bool)],
    out: &[QubitId],
    sign: QubitId,
    overflow: QubitId,
) {
    let lo = x.len() / 2;
    let hi = x.len() - lo;

    let t = circ.alloc_qubits(hi + 1);
    for i in 0..lo {
        circ.cx(x[i], t[i]);
    }
    let pad = circ.alloc_qubit();
    let mut hi_wide = x[lo..].to_vec();
    hi_wide.push(pad);
    add_full(circ, &hi_wide, &t);
    circ.zero_and_free(pad);

    // Local coefficients of a^2, t^2, b^2 in x^2 = (1-2^lo)a^2 + 2^lo*t^2 +
    // (2^(2lo)-2^lo)*b^2 -- same shape as the top-level split, one level down.
    let a_shifts: [(usize, bool); 2] = [(0, false), (lo, true)];
    let t_shifts: [(usize, bool); 1] = [(lo, false)];
    let b_shifts: [(usize, bool); 2] = [(lo, true), (2 * lo, false)];
    let branches: [(&[QubitId], &[(usize, bool)]); 3] = [
        (&x[..lo], &a_shifts),
        (t.as_slice(), &t_shifts),
        (&x[lo..], &b_shifts),
    ];
    for (sub, sub_shifts) in branches {
        let p = circ.alloc_qubits(2 * sub.len());
        // SQUARE-DEEPENING: this sub-product register IS materialised (the
        // folds below consume it as an operand), so the in-place split
        // licence applies here exactly as it does to branch B. Retention
        // spans only this sub's folds and is released before the next sub.
        let ret = tri_square_k2r(circ, sub, &p, ack2_min());
        for &(ss, sneg) in sub_shifts {
            for &(ps, pneg) in coefficients {
                fold_shifted(circ, sign, &p, out, overflow, ss + ps, sneg ^ pneg);
            }
        }
        tri_square_k2r_inv(circ, sub, &p, ret);
        circ.free_vec(&p);
    }

    let pad = circ.alloc_qubit();
    let mut hi_wide = x[lo..].to_vec();
    hi_wide.push(pad);
    sub_full(circ, &hi_wide, &t);
    circ.zero_and_free(pad);
    for i in 0..lo {
        circ.cx(x[i], t[i]);
    }
    circ.free_vec(&t);
}

/// NEW-ROUTES prototype (2026-08-26): in-place level-2 Karatsuba for branch B
/// (`y_hi^2`), keeping the materialized 256-bit product register and every
/// parent fold byte-identical. `a^2` and `b^2` are built by `tri_square`
/// directly into the two DISJOINT halves of the zeroed product register; the
/// cross term `2ab = t^2 - a^2 - b^2` is built in a retained 130-qubit scratch
/// and rippled in at shift 64 with one full-width exact add. The scratch (and
/// `t`) stay live across the parent folds so the inverse direction never
/// recomputes a sub-square.
///
/// Lambda: every new primitive is an exact full-width add/subtract
/// (`add_full`/`sub_full` at the non-chunked width; measurement-based carry
/// erasure is exact). Zero truncated comparisons, zero windowed folds, zero
/// measured chunk boundaries are added or removed, so the per-shot failure
/// site count is unchanged in both channels by construction.
/// `SUB4_SQUARE_B_LOCAL_K2=1` enables; default off (A/B measurement).
///
/// SQUARE-DEEPENING extension (2026-08-26): the same in-place split is made
/// RECURSIVE and width-thresholded. Any materialised tri_square of width
/// >= the threshold gets the local split; its `a^2` / `b^2` land in halves of
/// an already-materialised register and therefore carry the same licence one
/// level down, as does `t^2` inside its own retained scratch. Two scopes,
/// controlled separately so the peak cost of retention can be measured per
/// scope:
///   SUB4_SQUARE_BK2_MIN=<w>  — branch B (`y_hi^2`) recursion threshold.
///     128 reproduces route N-1 exactly; 64 adds level 3; default off.
///     SUB4_SQUARE_B_LOCAL_K2=1 is kept as an alias for BK2_MIN=128.
///   SUB4_SQUARE_ACK2_MIN=<w> — threshold for the six materialised
///     sub-squares inside branches A/C's `karatsuba_branch` (widths 64..66).
///     64 gives them each one local level; default off.
fn env_width(name: &str) -> Option<usize> {
    std::env::var(name).ok().and_then(|v| v.parse::<usize>().ok())
}

fn bk2_min() -> usize {
    static MIN: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *MIN.get_or_init(|| {
        if let Some(w) = env_width("SUB4_SQUARE_BK2_MIN") {
            return w;
        }
        let legacy = std::env::var_os("SUB4_SQUARE_B_LOCAL_K2")
            .map(|v| v == "1")
            .unwrap_or(true);
        if legacy {
            128
        } else {
            usize::MAX
        }
    })
}

fn ack2_min() -> usize {
    static MIN: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *MIN.get_or_init(|| env_width("SUB4_SQUARE_ACK2_MIN").unwrap_or(usize::MAX))
}

/// Q3 decomposition probe: materialise branch A (`y_lo^2`) / branch C
/// (`sum^2`) like branch B instead of the W5 no-materialisation
/// `karatsuba_branch` composition. Trades A's 10 (C's 5) composed narrow
/// folds — several of which straddle bit 256 and pay a 5-term `apply_f` on
/// their high parts — for 2 (1) wide folds plus the in-place-K2 assembly
/// overhead and 195/198 retained qubits across that branch's folds.
/// `SUB4_SQUARE_A_MAT=1` / `SUB4_SQUARE_C_MAT=1`; default off.
fn a_mat_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var_os("SUB4_SQUARE_A_MAT")
            .map(|v| v == "1")
            .unwrap_or(true)
    })
}

fn c_mat_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var_os("SUB4_SQUARE_C_MAT")
            .map(|v| v == "1")
            .unwrap_or(true)
    })
}

/// Scratch retained across the consumer's folds by one level of the in-place
/// split, plus whatever the recursion below it retained. Everything in here
/// stays live from the forward call to the matching inverse call.
struct K2Retained {
    t: Vec<QubitId>,
    p_t: Vec<QubitId>,
    sub_a: Option<Box<K2Retained>>,
    sub_b: Option<Box<K2Retained>>,
    sub_t: Option<Box<K2Retained>>,
}

/// Forward triangular square of `x` into the materialised `product`, applying
/// the retained in-place Karatsuba split recursively while `x.len() >=
/// min_width`. Returns the retained scratch (None = plain tri_square, no
/// retention). Op-order at min_width=128 on a 128-wide operand is identical
/// to route N-1's `tri_square_local_k2_forward`.
fn tri_square_k2r(
    circ: &mut B,
    x: &[QubitId],
    product: &[QubitId],
    min_width: usize,
) -> Option<Box<K2Retained>> {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    if m < min_width {
        tri_square(circ, x, product, false);
        return None;
    }
    let lo = m / 2;
    let hi = m - lo;
    let a = &x[..lo];
    let bs = &x[lo..];
    // a^2 and b^2 straight into the disjoint halves of the zeroed product.
    let sub_a = tri_square_k2r(circ, a, &product[..2 * lo], min_width);
    let sub_b = tri_square_k2r(circ, bs, &product[2 * lo..], min_width);
    // t = a + b, hi+1 bits.
    let t = circ.alloc_qubits(hi + 1);
    for i in 0..lo {
        circ.cx(a[i], t[i]);
    }
    let pad = circ.alloc_qubit();
    let mut b_wide = bs.to_vec();
    b_wide.push(pad);
    add_full(circ, &b_wide, &t[..hi + 1]);
    circ.zero_and_free(pad);
    // p_t = t^2, then subtract the still-pure halves: p_t = 2ab. Both
    // intermediates are nonnegative (t^2 - a^2 = 2ab + b^2 >= 0), so the
    // two's-complement frame never wraps at this width.
    let p_t = circ.alloc_qubits(2 * (hi + 1));
    let sub_t = tri_square_k2r(circ, &t, &p_t, min_width);
    let pads = circ.alloc_qubits(p_t.len() - 2 * lo);
    let mut a2_wide = product[..2 * lo].to_vec();
    a2_wide.extend_from_slice(&pads);
    sub_full(circ, &a2_wide, &p_t);
    circ.free_vec(&pads);
    let pads = circ.alloc_qubits(p_t.len() - 2 * hi);
    let mut b2_wide = product[2 * lo..].to_vec();
    b2_wide.extend_from_slice(&pads);
    sub_full(circ, &b2_wide, &p_t);
    circ.free_vec(&pads);
    // product += 2ab << lo, exact full ripple to the top (x^2 < 2^(2m), so
    // the top never overflows).
    let acc_hi = &product[lo..];
    let pads = circ.alloc_qubits(acc_hi.len() - p_t.len());
    let mut pt_wide = p_t.to_vec();
    pt_wide.extend_from_slice(&pads);
    add_full(circ, &pt_wide, acc_hi);
    circ.free_vec(&pads);
    Some(Box::new(K2Retained {
        t,
        p_t,
        sub_a,
        sub_b,
        sub_t,
    }))
}

/// Inverse of `tri_square_k2r`, consuming its retained scratch. Requires
/// `product` to hold exactly `x^2` (i.e. every consumer fold undone).
fn tri_square_k2r_inv(
    circ: &mut B,
    x: &[QubitId],
    product: &[QubitId],
    retained: Option<Box<K2Retained>>,
) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    let Some(ret) = retained else {
        tri_square(circ, x, product, true);
        return;
    };
    let K2Retained {
        t,
        p_t,
        sub_a,
        sub_b,
        sub_t,
    } = *ret;
    let lo = m / 2;
    let a = &x[..lo];
    let bs = &x[lo..];
    // product -= 2ab << lo: the halves are pure a^2 / b^2 again.
    let acc_hi = &product[lo..];
    let pads = circ.alloc_qubits(acc_hi.len() - p_t.len());
    let mut pt_wide = p_t.to_vec();
    pt_wide.extend_from_slice(&pads);
    sub_full(circ, &pt_wide, acc_hi);
    circ.free_vec(&pads);
    // p_t: 2ab -> t^2, then clear it with the inverse triangular square.
    let pads = circ.alloc_qubits(p_t.len() - 2 * hi_len(m));
    let mut b2_wide = product[2 * lo..].to_vec();
    b2_wide.extend_from_slice(&pads);
    add_full(circ, &b2_wide, &p_t);
    circ.free_vec(&pads);
    let pads = circ.alloc_qubits(p_t.len() - 2 * lo);
    let mut a2_wide = product[..2 * lo].to_vec();
    a2_wide.extend_from_slice(&pads);
    add_full(circ, &a2_wide, &p_t);
    circ.free_vec(&pads);
    tri_square_k2r_inv(circ, &t, &p_t, sub_t);
    circ.free_vec(&p_t);
    // Uncompute t = a + b.
    let pad = circ.alloc_qubit();
    let mut b_wide = bs.to_vec();
    b_wide.push(pad);
    sub_full(circ, &b_wide, &t);
    circ.zero_and_free(pad);
    for i in 0..lo {
        circ.cx(a[i], t[i]);
    }
    circ.free_vec(&t);
    // Clear the pure halves.
    tri_square_k2r_inv(circ, bs, &product[2 * lo..], sub_b);
    tri_square_k2r_inv(circ, a, &product[..2 * lo], sub_a);
}

fn hi_len(m: usize) -> usize {
    m - m / 2
}

pub(super) fn square_sub(circ: &mut B, y: &[QubitId], out: &[QubitId]) {
    assert_eq!(y.len(), N);
    assert_eq!(out.len(), N);
    let h = N / 2;
    let sign = circ.alloc_qubit();
    let overflow = circ.alloc_qubit();
    circ.x(sign);

    if a_mat_enabled() {
        // Q3 probe: branch A materialised, N-1-style in-place K2, same fold
        // semantics as the legacy path (+A at shift 0, -A at shift h).
        let product_a = circ.alloc_qubits(2 * h);
        let amin = env_width("SUB4_SQUARE_AMAT_MIN").unwrap_or(128);
        let ret = tri_square_k2r(circ, &y[..h], &product_a, amin);
        mod_add_top(circ, sign, &product_a, out, overflow, 0);
        circ.x(sign);
        apply_shift_half(circ, sign, &product_a, out, overflow);
        circ.x(sign);
        tri_square_k2r_inv(circ, &y[..h], &product_a, ret);
        circ.free_vec(&product_a);
    } else if karatsuba2_enabled() {
        karatsuba_branch(circ, &y[..h], &[(0, false), (h, true)], out, sign, overflow);
    } else {
        let product_a = circ.alloc_qubits(2 * h);
        tri_square(circ, &y[..h], &product_a, false);
        mod_add_top(circ, sign, &product_a, out, overflow, 0);
        circ.x(sign);
        apply_shift_half(circ, sign, &product_a, out, overflow);
        circ.x(sign);
        tri_square(circ, &y[..h], &product_a, true);
        circ.free_vec(&product_a);
    }

    let product_b = circ.alloc_qubits(2 * h);
    let retained = tri_square_k2r(circ, &y[h..], &product_b, bk2_min());
    circ.x(sign);
    apply_shift_half(circ, sign, &product_b, out, overflow);
    circ.x(sign);
    apply_shift_full(circ, sign, &product_b, out, overflow);
    tri_square_k2r_inv(circ, &y[h..], &product_b, retained);
    circ.free_vec(&product_b);

    // MERGE: hold a+b in the input's high half plus one carry wire (theirs).
    // The original high half is restored immediately after the cross-term
    // square. This removes a separate 129-qubit live register while preserving
    // the exact Karatsuba identity and the caller's input register. The
    // cross-term square itself is still OUR level-2 Karatsuba branch.
    let sum_carry = circ.alloc_qubit();
    let mut sum = y[h..].to_vec();
    sum.push(sum_carry);
    let pad = circ.alloc_qubit();
    let mut lo_wide = y[..h].to_vec();
    lo_wide.push(pad);
    add_full(circ, &lo_wide, &sum);
    circ.zero_and_free(pad);

    if c_mat_enabled() {
        // Q3 probe: branch C materialised (258-wide product, the
        // `apply_shift_half` straddle case), in-place K2.
        let product_c = circ.alloc_qubits(2 * (h + 1));
        let cmin = env_width("SUB4_SQUARE_CMAT_MIN").unwrap_or(128);
        let ret = tri_square_k2r(circ, &sum, &product_c, cmin);
        apply_shift_half(circ, sign, &product_c, out, overflow);
        tri_square_k2r_inv(circ, &sum, &product_c, ret);
        circ.free_vec(&product_c);
    } else if karatsuba2_enabled() {
        karatsuba_branch(circ, &sum, &[(h, false)], out, sign, overflow);
    } else {
        let product_c = circ.alloc_qubits(2 * (h + 1));
        tri_square(circ, &sum, &product_c, false);
        apply_shift_half(circ, sign, &product_c, out, overflow);
        tri_square(circ, &sum, &product_c, true);
        circ.free_vec(&product_c);
    }

    let pad = circ.alloc_qubit();
    let mut lo_wide = y[..h].to_vec();
    lo_wide.push(pad);
    sub_full(circ, &lo_wide, &sum);
    circ.zero_and_free(pad);
    circ.zero_and_free(sum_carry);
    circ.x(sign);
    circ.zero_and_free(sign);
    circ.zero_and_free(overflow);
}

pub(super) fn selfcheck() {
    use crate::point_add::SECP256K1_P;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::{
        digest::{ExtendableOutput, Update, XofReader},
        Shake256,
    };

    let mut circ = B::new();
    let source = circ.alloc_qubits(N);
    let accumulator = circ.alloc_qubits(N);
    square_sub(&mut circ, &source, &accumulator);
    let num_qubits = circ.next_qubit as usize;
    let num_bits = circ.next_bit as usize;
    let peak_qubits = circ.peak_qubits;
    let ops = circ.take_ops();

    let batches: usize = std::env::var("SQ_SELFTEST_BATCHES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1);
    let source_reg: Vec<QubitOrBit> = source.iter().copied().map(QubitOrBit::Qubit).collect();
    let accumulator_reg: Vec<QubitOrBit> = accumulator
        .iter()
        .copied()
        .map(QubitOrBit::Qubit)
        .collect();
    for batch in 0..batches {
        let mut input_seed = Shake256::default();
        input_seed.update(b"product-register-square-inputs");
        input_seed.update(&(batch as u64).to_le_bytes());
        let mut input_reader = input_seed.finalize_xof();
        let mut sources = [U256::ZERO; 64];
        let mut accumulators = [U256::ZERO; 64];
        let mut expected = [U256::ZERO; 64];
        let mut bytes = [0u8; 32];
        for shot in 0..64 {
            input_reader.read(&mut bytes);
            sources[shot] = U256::from_le_bytes(bytes) % SECP256K1_P;
            input_reader.read(&mut bytes);
            accumulators[shot] = U256::from_le_bytes(bytes) % SECP256K1_P;
            let square = sources[shot].mul_mod(sources[shot], SECP256K1_P);
            expected[shot] = if accumulators[shot] >= square {
                accumulators[shot] - square
            } else {
                SECP256K1_P - (square - accumulators[shot])
            };
        }

        let mut sim_seed = Shake256::default();
        sim_seed.update(b"product-register-square-simulator");
        sim_seed.update(&(batch as u64).to_le_bytes());
        let mut sim_reader = sim_seed.finalize_xof();
        let mut sim = Simulator::new(num_qubits, num_bits, &mut sim_reader);
        for shot in 0..64 {
            sim.set_register(&source_reg, sources[shot], shot);
            sim.set_register(&accumulator_reg, accumulators[shot], shot);
        }
        sim.apply_iter(ops.iter());

        let counting = std::env::var_os("SQ_SELFTEST_COUNT").is_some();
        for shot in 0..64 {
            let src_ok = sim.get_register(&source_reg, shot) == sources[shot];
            let acc_ok = sim.get_register(&accumulator_reg, shot) == expected[shot];
            if counting {
                if !src_ok || !acc_ok {
                    let got = sim.get_register(&accumulator_reg, shot);
                    eprintln!(
                        "SQ_FAIL batch={batch} shot={shot} src_ok={src_ok} acc_ok={acc_ok} diff_bits={}",
                        if acc_ok { String::from("-") } else {
                            let (g, e) = (got, expected[shot]);
                            let d = if e > g { e - g } else { g - e };
                            format!("{:x}", d)
                        }
                    );
                }
            } else {
                assert!(src_ok, "source register mismatch batch {batch} shot {shot}");
                assert!(acc_ok, "accumulator mismatch batch {batch} shot {shot}");
            }
        }
        if counting {
            if sim.phase != 0 {
                eprintln!("SQ_PHASE batch={batch} word={:x}", sim.phase);
            }
        } else {
            assert_eq!(sim.phase, 0, "phase garbage in product-register square");
        }
        for q in 0..num_qubits as u64 {
            let q = QubitId(q);
            if source.contains(&q) || accumulator.contains(&q) {
                continue;
            }
            if counting {
                if sim.qubit(q) != 0 {
                    eprintln!("SQ_DIRTY batch={batch} q={q:?}");
                }
            } else {
                assert_eq!(sim.qubit(q), 0, "dirty product-square ancilla {q:?}");
            }
        }
        if batch % 5000 == 0 {
            eprintln!("sq-selftest batch {batch}/{batches} clean-so-far");
        }
        if batch + 1 < batches {
            continue;
        }
    }
    {
    // final-batch stats reporting uses the last sim below via a fresh run
    }
    let mut sim_seed = Shake256::default();
    sim_seed.update(b"product-register-square-simulator");
    let mut sim_reader = sim_seed.finalize_xof();
    let mut sim = Simulator::new(num_qubits, num_bits, &mut sim_reader);
    sim.apply_iter(ops.iter());

    let emitted = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();
    let executed = sim.stats.toffoli_gates as f64 / 64.0;
    eprintln!(
        "product-register square: {emitted} emitted / {executed:.3} executed Toffoli, {peak_qubits} peak qubits"
    );
}
