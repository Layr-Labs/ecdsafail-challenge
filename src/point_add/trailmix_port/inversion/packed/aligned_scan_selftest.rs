//! Selftest for `aligned_scan_top` (D11) / `aligned_scan_bottom` (M1) on REAL
//! packed-prefix states: the exact `pz_prefix` recurrence of
//! `tools/packed_prefix_model.py` (verbatim: single-q Kaliski step, 530 rows) is
//! run in U512 on Shake256-seeded inputs; every division row gives a D11 case
//! (R1 in the s-frame, `e_A = e_A_old - off` as after D7b), every multiply row
//! an M1 case (R2 in the LSB frame). Per case, forward then inverse on the same
//! data (bit-parallel `Simulator`, 64 shots per circuit): values, phase == 0,
//! every freed ancilla == 0 (`checked_apply` asserts at each reset), and on the
//! support the design's frame claims (`k = n_w - 1 + off - d`, `g = gap`) and
//! the exponent results (`e_A_new = bl(A_new)`, `e_ca -> 0` / stays 0).
//! Required classes (design 10 / refuter fix 7) are counted and asserted
//! non-empty: R1 gap = 0 (cb's MSB at wire e_A), `e_A = W_A` with off = 0,
//! e_B < 32 (window wraps A's low bits / cb below the MSB), foreign 1-bits below
//! the scanned MSB, W_A < 32, terminal rows (A_new = 0, garbage k), synthetic
//! all-zero windows, first multiplies (ca_old = 0) with e_B in [226, 256] and
//! with e_B <= 225 (all-zero window -> sentinel), draining multiplies (A = 0,
//! B = 1), gap in [0, 25], gate = 0 rows. Prints measured Toffoli.
//!
//! Adversarial additions (review, 2026-09-13), all forward + inverse on the same
//! data with the same checks:
//! * synthetic D11 rows built in the model's own terms (`synth_div`: B, R =
//!   A_new >> s with `bl(R) = E - d`, A_old = ((R + B) << s) + low) so that the
//!   drop `d` sweeps 1..31+off for both `off` values (MSB at every window index
//!   incl. the top k = n_w-1 and the bottom k = 0), with tight packing (R1 gap
//!   0, cb all ones), all-ones low bits (dense foreign bits in the wrap), the
//!   empty-field rows `d >= E` (R = 0, the MSB in A's wrapped low bits), `e_A =
//!   W_A` with off = 0, `e_B = lo_B` (t7 = 127 on a 159-wire ring) and `e_B =
//!   W_A` (t7 = 0), rings of 32 / 64 / 128 wires (skipped or degenerate layers),
//!   L = 1, and the `drop_bound` miss rows `d = 32 + off` (window all zero ->
//!   the sentinel 63 is asserted: the miss is detectable);
//! * synthetic M1 rows at t7 = 127 / t7 = 0, `e_B = lo_B`, `W_B - lo_B = 127`,
//!   B all ones (the wrapped bits start exactly at 257 - e_B: the `nz` compare's
//!   boundary `g == u`) and B = 2^(e_B-1);
//! * random garbage rows (ring, exponents 0..511, gate 0/1): the inverse must
//!   restore the data exactly whatever the input (the design's reverse-direction
//!   rule, off the support);
//! * D11 without `MIDQ_KG_ZERO_LAYER` (the frame claims do not need it; the
//!   all-zero window then deposits 0);
//! * a pass under the production route (`configure_sub1000_trailmix_route`:
//!   LOWQ_ONE_A_ELIM, LOWQ_COMPACT_KGANC, MIDQ_CHUNK_COMPARE + VARIABLE_CHUNKS,
//!   ...) with `MIDQ_CHUNKED_PREFIX` forced off, because the route's default
//!   `MIDQ_CHUNKED_PREFIX=1` routes the ladder through `chunked_bitlength::xor`,
//!   which has no k = -1 layer (found by this review: M1 then erases e_ca by a
//!   garbage amount on every all-zero window while the `MIDQ_KG_ZERO_LAYER`
//!   assert still passes; `aligned_scan` now refuses to build in that case).

use super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const NSTEPS: usize = 530;
const NINPUTS: usize = 64;
const RING: usize = 257;
/// `step` marker of a synthetic on-support row (not from a trace).
const SYNTH: usize = usize::MAX;
/// `step` marker of a synthetic D11 row that is an intentional `drop_bound`
/// miss (`d > n_w - 1 + off`): no value claim, but the window must read as
/// all-zero (sentinel) when it holds no wrapped wire.
const SYNTH_MISS: usize = usize::MAX - 1;
/// The all-zero-window deposit: 63 with the k = -1 layer, 0 without it.
fn sentinel() -> usize {
    if kg_zero_layer_enabled() { (1 << POS_BITS) - 1 } else { 0 }
}

fn p() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}

fn bl(x: &U512) -> usize {
    x.bit_len()
}

#[derive(Clone)]
struct DivRow {
    step: usize,
    a_old: U512,
    b: U512,
    cb: U512,
    s: usize,
    off: bool,
    a_new: U512,
}

#[derive(Clone)]
struct MulRow {
    step: usize,
    a: U512,
    b: U512,
    ca_old: U512,
}

/// Any row (for gate = 0 filler shots and the envelope): pre-step values.
#[derive(Clone)]
struct Pre {
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
}

struct Trace {
    pre: Vec<Pre>,             // per step
    div: Vec<Option<DivRow>>,  // per step
    mul: Vec<Option<MulRow>>,  // per step
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) with row recording.
fn trace(x_orig: U512) -> Trace {
    let p = p();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, U512::from(1u64), U512::ZERO);
    let one = U512::from(1u64);
    let mut pre = Vec::with_capacity(NSTEPS);
    let mut div = Vec::with_capacity(NSTEPS);
    let mut mul = Vec::with_capacity(NSTEPS);
    for step in 0..NSTEPS {
        assert!(a * cb + b * (ca + q * cb) == p, "row invariant");
        pre.push(Pre { a, b, ca, cb });
        let mut drow = None;
        let mut mrow = None;
        if !(a.is_zero() && b == one && q.is_zero()) {
            if a < b && !q.is_zero() {
                let s2 = q.trailing_zeros();
                mrow = Some(MulRow { step, a, b, ca_old: ca });
                q ^= one << s2;
                ca += cb << s2;
            }
            if ca < cb {
                let mut s = bl(&a) as i64 - bl(&b) as i64;
                let mut off = false;
                if s >= 0 && a < (b << (s as usize)) {
                    s -= 1;
                    off = true;
                }
                if s >= 0 {
                    let s = s as usize;
                    let bsh = b << s;
                    if a >= bsh {
                        let a_new = a - bsh;
                        drow = Some(DivRow { step, a_old: a, b, cb, s, off, a_new });
                        a = a_new;
                        q ^= one << s;
                    }
                }
            }
            if q.is_zero() && !a.is_zero() {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut ca, &mut cb);
            }
        }
        div.push(drow);
        mul.push(mrow);
    }
    assert!(a.is_zero() && q.is_zero(), "input did not terminate by {NSTEPS}");
    Trace { pre, div, mul }
}

/// LSB-frame ring content: value bits at wires [0, bl v), coefficient bit j at
/// wire 256 - j. Asserts the packing invariant (no overlap).
fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

/// D11 s-frame of a division row: the LSB-frame final R1 = [A_new | gap | cb]
/// rotated DOWN by s on the ring [0, W_A) (wire w holds LSB-frame wire (w+s) mod W_A).
fn s_frame(row: &DivRow, w_a: usize) -> Vec<bool> {
    let lsb = ring_lsb(&row.a_new, &row.cb);
    (0..RING)
        .map(|w| if w < w_a { lsb[(w + row.s) % w_a] } else { lsb[w] })
        .collect()
}

fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}

fn one() -> U512 {
    U512::from(1u64)
}

fn pow2(w: usize) -> U512 {
    one() << w
}

/// Uniform-ish random value below `n` (`n != 0`).
fn rnd_below(rng: &mut impl XofReader, n: U512) -> U512 {
    assert!(!n.is_zero());
    let mut bytes = [0u8; 64];
    rng.read(&mut bytes[..40]);
    U512::from_le_bytes(bytes) % n
}

/// Random value of bit-length exactly `w` (0 for `w = 0`); all ones when `dense`.
fn rnd_bl(rng: &mut impl XofReader, w: usize, dense: bool) -> U512 {
    if w == 0 {
        return U512::ZERO;
    }
    if dense {
        return pow2(w) - one();
    }
    pow2(w - 1) + rnd_below(rng, pow2(w - 1))
}

/// A division row in the model's own terms from the D11 quantities:
/// `B` with `bl(B) = e_B`; `R = A_new >> s` with `bl(R) = E - d` (`E = e_B +
/// off`); `A_old = ((R + B) << s) + low`, `A_new = (R << s) + low`; `cb` with
/// `bl(cb) = cb_bl`. `dense` makes `cb` and `low` all ones (foreign 1-bits
/// wherever the window can wrap). Regimes: `d < E` (the field holds R's MSB;
/// off = 0 needs `R + B < 2^e_B`, off = 1 needs `2^e_B - B <= R < B`) and `d >=
/// E` (R = 0, off = 0: the MSB is `low`'s, `bl(low) = E + s - d`). Returns
/// `None` when the quantities are not realisable (e.g. off = 1 with `e_B = 1`).
/// The result satisfies the model's own predicates: `s = bl(A_old) - bl(B) -
/// off`, `off = [A_old < B << (s+1)]`, `A_old >= B << s`, `d = bl(A_old) -
/// bl(A_new)`.
fn synth_div(
    rng: &mut impl XofReader,
    e_b: usize,
    off: bool,
    s: usize,
    d: usize,
    cb_bl: usize,
    dense: bool,
    step: usize,
) -> Option<DivRow> {
    if e_b == 0 || d == 0 || cb_bl == 0 {
        return None;
    }
    let e = e_b + usize::from(off);
    let (a_old, a_new, b) = if d < e {
        let r_bl = e - d;
        let mut b = rnd_bl(rng, e_b, false);
        // valid R range [lo, hi)
        let range = |b: &U512| -> (U512, U512) {
            if !off {
                (pow2(r_bl - 1), pow2(r_bl).min(pow2(e_b) - *b))
            } else {
                (pow2(r_bl - 1).max(pow2(e_b) - *b), pow2(r_bl).min(*b))
            }
        };
        let (mut lo, mut hi) = range(&b);
        if lo >= hi {
            // fall back to the extreme B that always admits the range
            b = if !off { pow2(e_b - 1) } else { pow2(e_b) - one() };
            (lo, hi) = range(&b);
            if lo >= hi {
                return None;
            }
        }
        let r = lo + rnd_below(rng, hi - lo);
        // A's low s bits: any value below 2^s (all ones when dense)
        let low = if s == 0 { U512::ZERO } else if dense { pow2(s) - one() } else { rnd_below(rng, pow2(s)) };
        (((r + b) << s) + low, (r << s) + low, b)
    } else {
        // empty field: off = 0, R = 0, the MSB is low's
        if off || s == 0 || d > e + s - 1 {
            return None;
        }
        let b = rnd_bl(rng, e_b, false);
        let low = rnd_bl(rng, e + s - d, dense);
        ((b << s) + low, low, b)
    };
    let ea_old = bl(&a_old);
    if ea_old + cb_bl > RING {
        return None;
    }
    let cb = rnd_bl(rng, cb_bl, dense);
    // the model's own predicates
    assert_eq!(ea_old, e + s);
    assert_eq!(bl(&a_new), ea_old - d);
    assert!(a_old >= (b << s));
    // the model: s_raw = bl(A) - bl(B); off = [A < B << s_raw]; s = s_raw - off
    let s_raw = bl(&a_old) - bl(&b);
    assert_eq!(s_raw, s + usize::from(off));
    assert_eq!(a_old < (b << s_raw), off, "off predicate");
    Some(DivRow { step, a_old, b, cb, s, off, a_new })
}

/// A multiply row from the M1 quantities: `B` with `bl(B) = e_B` (`b_kind`: 0
/// random, 1 all ones, 2 = 2^(e_B-1)), `ca_old` with `bl = 257 - e_B - gap`
/// (0 when `gap` is `None`), random or all ones.
fn synth_mul(rng: &mut impl XofReader, e_b: usize, gap: Option<usize>, b_kind: u8, dense_ca: bool) -> Option<MulRow> {
    if e_b == 0 {
        return None;
    }
    let b = match b_kind {
        0 => rnd_bl(rng, e_b, false),
        1 => pow2(e_b) - one(),
        _ => pow2(e_b - 1),
    };
    let ca_old = match gap {
        None => U512::ZERO,
        Some(g) => {
            if e_b + g + 1 > RING {
                return None;
            }
            rnd_bl(rng, RING - e_b - g, dense_ca)
        }
    };
    Some(MulRow { step: SYNTH, a: one(), b, ca_old })
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Peak number of live scratch wires above the data registers: a non-data
/// qubit is live from its first touch after its last reset (`R`, emitted by
/// `zero_and_free`) until that reset.
fn peak_scratch(ops: &[Op], data: &[QubitId]) -> usize {
    use crate::circuit::NO_QUBIT;
    let mut live: std::collections::HashSet<u64> = std::collections::HashSet::new();
    let data: std::collections::HashSet<u64> = data.iter().map(|q| q.0).collect();
    let mut peak = 0usize;
    for op in ops {
        for q in [op.q_control2, op.q_control1, op.q_target] {
            if q != NO_QUBIT && !data.contains(&q.0) {
                live.insert(q.0);
            }
        }
        peak = peak.max(live.len());
        if op.kind == OperationType::R {
            live.remove(&op.q_target.0);
        }
    }
    peak
}

struct Harness {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    t: usize,
    scratch: usize,
}

fn ids(regs: &[&[QReg]]) -> Vec<QubitId> {
    regs.iter().flat_map(|r| r.iter().map(|q| QubitId(q.id().into()))).collect()
}

/// D11 harness: data wires [r1(257) | e_b(9) | e_a(9) | gate | wit(6)]; the hook
/// XORs pos into wit (self-inverse) so the test sees what D11t would see.
fn build_top(w_a: usize, lo_b: usize, inverse: bool) -> Harness {
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("r1", RING);
    let e_b = c.alloc_qreg_bits("e_b", EXP_BITS);
    let e_a = c.alloc_qreg_bits("e_a", EXP_BITS);
    let gate = c.alloc_qreg("gate");
    let wit = c.alloc_qreg_bits("wit", POS_BITS);
    let ids = ids(&[&r1, &e_b, &e_a, std::slice::from_ref(&gate), &wit]);
    let start = c.b.ops.len();
    aligned_scan_top(&mut c, &r1, &e_b, &e_a, &gate, w_a, lo_b, inverse, |c, pos| {
        for (p, w) in pos.iter().zip(&wit) {
            c.cx(p, w);
        }
    });
    let t = toffoli(&c.b.ops[start..]);
    let scratch = peak_scratch(&c.b.ops[start..], &ids);
    Harness { ops: c.b.ops.clone(), ids, t, scratch }
}

/// M1 harness: data wires [r2(257) | e_b(9) | e_ca(9) | gate].
fn build_bottom(w_b: usize, lo_b: usize, inverse: bool) -> Harness {
    let mut c = Circuit::new();
    let r2 = c.alloc_qreg_bits("r2", RING);
    let e_b = c.alloc_qreg_bits("e_b", EXP_BITS);
    let e_ca = c.alloc_qreg_bits("e_ca", EXP_BITS);
    let gate = c.alloc_qreg("gate");
    let ids = ids(&[&r2, &e_b, &e_ca, std::slice::from_ref(&gate)]);
    let start = c.b.ops.len();
    aligned_scan_bottom(&mut c, &r2, &e_b, &e_ca, &gate, w_b, lo_b, inverse);
    let t = toffoli(&c.b.ops[start..]);
    let scratch = peak_scratch(&c.b.ops[start..], &ids);
    Harness { ops: c.b.ops.clone(), ids, t, scratch }
}

/// Run up to 64 shots: load the data wires, apply with reset checks, assert
/// phase 0 and every non-data qubit 0, return the data wires per shot.
fn simulate(h: &Harness, shots: &[Vec<bool>], label: &str) -> Vec<Vec<bool>> {
    assert!(!shots.is_empty() && shots.len() <= 64);
    let (nq, nb, _, _) = analyze_ops(h.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-aligned-scan-sim-v1");
    seed.update(label.as_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for (shot, data) in shots.iter().enumerate() {
        assert_eq!(data.len(), h.ids.len());
        for (i, &id) in h.ids.iter().enumerate() {
            if data[i] {
                *sim.qubit_mut(id) |= 1u64 << shot;
            }
        }
    }
    let mask = u64::MAX >> (64 - shots.len());
    super::super::super::predicate_clear_selftest::checked_apply(&mut sim, &h.ops, mask);
    assert_eq!(sim.phase & mask, 0, "{label}: phase");
    let out: Vec<Vec<bool>> = (0..shots.len())
        .map(|shot| h.ids.iter().map(|&id| (sim.qubit(id) >> shot) & 1 == 1).collect())
        .collect();
    for &id in &h.ids {
        *sim.qubit_mut(id) = 0;
    }
    assert!(sim.qubits.iter().all(|&q| q & mask == 0), "{label}: dirty ancilla");
    out
}

#[derive(Default, Debug)]
struct Counts {
    div_rows: usize,
    div_support: usize,
    gap1_zero: usize,
    ea_eq_wa_off0: usize,
    eb_lt_32: usize,
    foreign_below: usize,
    wa_lt_32: usize,
    terminal: usize,
    allzero_win: usize,
    drop_bound_miss: usize,
    off1: usize,
    d_max: usize,
    mul_rows: usize,
    mul_support: usize,
    first_mul: usize,
    first_mul_hi_eb: usize,
    first_mul_lo_eb: usize,
    draining: usize,
    gap_bound_miss: usize,
    gap2_max: usize,
    gap2_synth_max: usize,
    gate0: usize,
    inverse_checked: usize,
    // review additions
    synth_div: usize,
    synth_div_miss: usize,
    synth_d_max: usize,
    k_top: usize,
    k_zero: usize,
    empty_field: usize,
    t7_zero_top: usize,
    t7_max_top: usize,
    ring_gt_128_top: usize,
    ring_pow2_top: usize,
    synth_ea_eq_wa_off0: usize,
    synth_gap1_zero: usize,
    t7_zero_bot: usize,
    t7_max_bot: usize,
    nz_boundary: usize,
    b_all_ones_wrap: usize,
    garbage_rt: usize,
    zero_layer_off: usize,
    route_rt: usize,
}

/// One D11 shot: (data, expected, class flags). `gate` chooses the active row.
struct TopShot {
    data: Vec<bool>,
    expect: Vec<bool>,
}

fn top_shot(row: &DivRow, w_a: usize, lo_b: usize, gate: bool, zero_cb: bool, cnt: &mut Counts) -> TopShot {
    let (l, _s, n_w) = top_geometry(w_a, lo_b);
    let e_a_old = bl(&row.a_old);
    let e_b = bl(&row.b);
    let e_cb = bl(&row.cb);
    let off = usize::from(row.off);
    let e = e_b + off;
    let d = e_a_old - bl(&row.a_new);
    let terminal = row.a_new.is_zero();
    assert!(e_a_old <= w_a && lo_b <= e_b && e_b <= w_a, "row outside the config");
    let row2 = if zero_cb { DivRow { cb: U512::ZERO, ..row.clone() } } else { row.clone() };
    let sf = s_frame(&row2, w_a);
    // classical window after the rotation by t7 = W_A - e_B on [L, W_A)
    let s_ring = w_a - l;
    let t7 = w_a - e_b;
    let rot: Vec<bool> = (0..RING)
        .map(|w| if w >= l && w < w_a { sf[l + (w - l + s_ring - t7 % s_ring) % s_ring] } else { sf[w] })
        .collect();
    let win = &rot[w_a - n_w..w_a];
    let all_zero = !win.iter().any(|&b| b);
    let k = win.iter().rposition(|&b| b).map_or(sentinel(), |j| j);
    let e_a_in = e_a_old - off;
    let e_a_out = if gate { (e_a_in + k + (1 << EXP_BITS) - (n_w - 1)) % (1 << EXP_BITS) } else { e_a_in };
    // classes
    cnt.div_rows += 1;
    if !gate { cnt.gate0 += 1; }
    if terminal { cnt.terminal += 1; }
    if all_zero { cnt.allzero_win += 1; }
    let synthetic = row.step == SYNTH || row.step == SYNTH_MISS;
    if gate && synthetic {
        if row.step == SYNTH_MISS {
            // intentional drop_bound miss: R's MSB below the window. Without a
            // wrapped wire (e_B >= 32) the window is R's zeros only, so the
            // ladder must deposit the sentinel: the miss is detectable.
            assert!(d > n_w - 1 + off, "SYNTH_MISS row is on the support");
            cnt.synth_div_miss += 1;
            if e_b >= WINDOW {
                assert!(all_zero, "drop_bound miss window not all zero: e_B {e_b} d {d}");
                assert_eq!(k, sentinel());
            }
        } else {
            assert!(d <= n_w - 1 + off, "synthetic row off the support: d {d} n_w {n_w} off {off}");
            cnt.synth_div += 1;
            cnt.synth_d_max = cnt.synth_d_max.max(d);
            if k == n_w - 1 { cnt.k_top += 1; }
            if k == 0 { cnt.k_zero += 1; }
            if bl(&row.a_new) <= row.s { cnt.empty_field += 1; }
            if t7 == 0 { cnt.t7_zero_top += 1; }
            if t7 == (1 << T7_BITS) - 1 { cnt.t7_max_top += 1; }
            if s_ring > (1 << T7_BITS) { cnt.ring_gt_128_top += 1; }
            if s_ring.is_power_of_two() && s_ring >= 2 { cnt.ring_pow2_top += 1; }
            if e_a_old == w_a && !row.off { cnt.synth_ea_eq_wa_off0 += 1; }
            if RING - e_a_old - e_cb == 0 { cnt.synth_gap1_zero += 1; }
        }
    }
    if gate && !terminal && !zero_cb && row.step != SYNTH_MISS {
        if RING - e_a_old - e_cb == 0 { cnt.gap1_zero += 1; }
        if e_a_old == w_a && !row.off { cnt.ea_eq_wa_off0 += 1; }
        if e_b < WINDOW { cnt.eb_lt_32 += 1; }
        if w_a < WINDOW { cnt.wa_lt_32 += 1; }
        if row.off { cnt.off1 += 1; }
        if !synthetic { cnt.d_max = cnt.d_max.max(d); }
        if d <= n_w - 1 + off {
            cnt.div_support += 1;
            // the design's frame claim on a real state
            assert_eq!(k, n_w - 1 + off - d, "D11 frame: step {} W_A {w_a} lo_B {lo_b} e_B {e_b} off {off} d {d}", row.step);
            assert_eq!(e_a_out, bl(&row.a_new), "D11 result: step {}", row.step);
            // foreign 1-bits below the MSB: window positions j < k whose source
            // s-frame wire is >= E (above the field) and holds 1
            let foreign = (0..k).any(|j| {
                let w = w_a - n_w + j;
                let src = l + (w - l + s_ring - t7 % s_ring) % s_ring;
                src >= e && sf[src]
            });
            if foreign { cnt.foreign_below += 1; }
        } else {
            cnt.drop_bound_miss += 1;
        }
    }
    let mut data = sf.clone();
    data.extend(bits_of(e_b, EXP_BITS));
    data.extend(bits_of(e_a_in, EXP_BITS));
    data.push(gate);
    data.extend(bits_of(0, POS_BITS));
    let mut expect = sf;
    expect.extend(bits_of(e_b, EXP_BITS));
    expect.extend(bits_of(e_a_out, EXP_BITS));
    expect.push(gate);
    expect.extend(bits_of(k, POS_BITS));
    TopShot { data, expect }
}

/// Filler D11 shot (gate = 0) from a non-division row: any content must be restored.
fn top_filler(pre: &Pre, cnt: &mut Counts) -> TopShot {
    let lsb = ring_lsb(&pre.a, &pre.cb);
    let mut data = lsb.clone();
    data.extend(bits_of(bl(&pre.b), EXP_BITS));
    data.extend(bits_of(bl(&pre.a), EXP_BITS));
    data.push(false);
    data.extend(bits_of(0, POS_BITS));
    cnt.gate0 += 1;
    // wit receives whatever pos the window yields; computed by the sim, so
    // compare everything except wit (masked below).
    TopShot { data: data.clone(), expect: data }
}

struct BotShot {
    data: Vec<bool>,
    expect: Vec<bool>,
}

fn bottom_shot(row: &MulRow, w_b: usize, lo_b: usize, gate: bool, cnt: &mut Counts) -> BotShot {
    let (top, s_ring) = bottom_geometry(w_b, lo_b);
    let e_b = bl(&row.b);
    let e_ca = bl(&row.ca_old);
    assert!(lo_b <= e_b && e_b <= w_b, "row outside the config");
    assert!(e_b >= 1);
    let lsb = ring_lsb(&row.b, &row.ca_old);
    let t7 = e_b - lo_b;
    let win: Vec<bool> = (0..WINDOW).map(|j| lsb[lo_b + (j + t7) % s_ring]).collect();
    let g = win.iter().position(|&b| b);
    let v = g.unwrap_or(256);
    let nz = v < RING - e_b;
    let e_ca_out = if gate && nz { (e_ca + (1 << EXP_BITS) - (RING - e_b - g.unwrap())) % (1 << EXP_BITS) } else { e_ca };
    cnt.mul_rows += 1;
    if !gate { cnt.gate0 += 1; }
    if gate {
        let first = row.ca_old.is_zero();
        if row.step == SYNTH {
            if t7 == 0 { cnt.t7_zero_bot += 1; }
            if t7 == (1 << T7_BITS) - 1 { cnt.t7_max_bot += 1; }
            // B all ones wrapping into the window: the first wrapped position
            // 257 - e_B (T = 257) holds a 1
            if row.b == pow2(e_b) - one() && top == RING && e_b + WINDOW > RING { cnt.b_all_ones_wrap += 1; }
        }
        if first {
            cnt.first_mul += 1;
            if e_b >= 226 { cnt.first_mul_hi_eb += 1; } else { cnt.first_mul_lo_eb += 1; }
            assert!(!nz, "M1 nz on ca_old = 0: step {} e_B {e_b} g {g:?}", row.step);
            assert_eq!(e_ca_out, 0);
            if g.is_none() { cnt.allzero_win += 1; }
            // the compare's boundary: the lowest wrapped 1 exactly at 257 - e_B
            if g == Some(RING - e_b) { cnt.nz_boundary += 1; }
            cnt.mul_support += 1;
        } else {
            let gap = RING - e_b - e_ca;
            if row.step == usize::MAX {
                cnt.gap2_synth_max = cnt.gap2_synth_max.max(gap);
            } else {
                cnt.gap2_max = cnt.gap2_max.max(gap);
            }
            if row.a.is_zero() { cnt.draining += 1; }
            if gap < WINDOW {
                assert_eq!(g, Some(gap), "M1 gap: step {} e_B {e_b} e_ca {e_ca}", row.step);
                assert!(nz, "M1 nz: step {}", row.step);
                assert_eq!(e_ca_out, 0, "M1 erase: step {}", row.step);
                cnt.mul_support += 1;
            } else {
                cnt.gap_bound_miss += 1;
            }
        }
        assert!(top <= RING);
    }
    let mut data = lsb.clone();
    data.extend(bits_of(e_b, EXP_BITS));
    data.extend(bits_of(e_ca, EXP_BITS));
    data.push(gate);
    let mut expect = lsb;
    expect.extend(bits_of(e_b, EXP_BITS));
    expect.extend(bits_of(e_ca_out, EXP_BITS));
    expect.push(gate);
    BotShot { data, expect }
}

fn bottom_filler(pre: &Pre, cnt: &mut Counts) -> BotShot {
    let lsb = ring_lsb(&pre.b, &pre.ca);
    let mut data = lsb;
    data.extend(bits_of(bl(&pre.b), EXP_BITS));
    data.extend(bits_of(bl(&pre.ca), EXP_BITS));
    data.push(false);
    cnt.gate0 += 1;
    BotShot { data: data.clone(), expect: data }
}

/// Forward on `shots`, check against `expect` (wit compared only where
/// `check_wit`), then inverse on the outputs must return `data`.
fn round_trip_top(w_a: usize, lo_b: usize, shots: &[TopShot], check_wit: &[bool], label: &str, cnt: &mut Counts) -> usize {
    let fwd = build_top(w_a, lo_b, false);
    let inv = build_top(w_a, lo_b, true);
    let data: Vec<Vec<bool>> = shots.iter().map(|s| s.data.clone()).collect();
    let out = simulate(&fwd, &data, &format!("{label}-fwd"));
    let n_data = RING + 2 * EXP_BITS + 1;
    for (i, (o, s)) in out.iter().zip(shots).enumerate() {
        let lim = if check_wit[i] { o.len() } else { n_data };
        assert_eq!(&o[..lim], &s.expect[..lim], "{label}: forward shot {i} (W_A {w_a} lo_B {lo_b})");
    }
    let back = simulate(&inv, &out, &format!("{label}-inv"));
    for (i, (b, s)) in back.iter().zip(shots).enumerate() {
        assert_eq!(b, &s.data, "{label}: inverse shot {i}");
    }
    cnt.inverse_checked += shots.len();
    fwd.t
}

fn round_trip_bottom(w_b: usize, lo_b: usize, shots: &[BotShot], label: &str, cnt: &mut Counts) -> usize {
    let fwd = build_bottom(w_b, lo_b, false);
    let inv = build_bottom(w_b, lo_b, true);
    let data: Vec<Vec<bool>> = shots.iter().map(|s| s.data.clone()).collect();
    let out = simulate(&fwd, &data, &format!("{label}-fwd"));
    for (i, (o, s)) in out.iter().zip(shots).enumerate() {
        assert_eq!(o, &s.expect, "{label}: forward shot {i} (W_B {w_b} lo_B {lo_b})");
    }
    let back = simulate(&inv, &out, &format!("{label}-inv"));
    for (i, (b, s)) in back.iter().zip(shots).enumerate() {
        assert_eq!(b, &s.data, "{label}: inverse shot {i}");
    }
    cnt.inverse_checked += shots.len();
    fwd.t
}

/// Reversibility off the support: random data (ring, exponents in [0, 512),
/// gate 0/1, witness) through forward then inverse must come back unchanged,
/// with phase 0 and clean ancillae at every reset (the circuits are exact
/// gate-inverses of each other for ANY input, not only on the support).
fn garbage_rows(rng: &mut impl XofReader, n_data: usize, shots: usize) -> Vec<Vec<bool>> {
    (0..shots)
        .map(|_| {
            let mut bytes = vec![0u8; n_data.div_ceil(8)];
            rng.read(&mut bytes);
            (0..n_data).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect()
        })
        .collect()
}

fn garbage_top(w_a: usize, lo_b: usize, rng: &mut impl XofReader, label: &str, cnt: &mut Counts) {
    let fwd = build_top(w_a, lo_b, false);
    let inv = build_top(w_a, lo_b, true);
    let data = garbage_rows(rng, fwd.ids.len(), 64);
    let out = simulate(&fwd, &data, &format!("{label}-fwd"));
    let back = simulate(&inv, &out, &format!("{label}-inv"));
    for (i, (b, d)) in back.iter().zip(&data).enumerate() {
        assert_eq!(b, d, "{label}: garbage inverse shot {i} (W_A {w_a} lo_B {lo_b})");
    }
    cnt.garbage_rt += data.len();
    cnt.inverse_checked += data.len();
}

fn garbage_bottom(w_b: usize, lo_b: usize, rng: &mut impl XofReader, label: &str, cnt: &mut Counts) {
    let fwd = build_bottom(w_b, lo_b, false);
    let inv = build_bottom(w_b, lo_b, true);
    let data = garbage_rows(rng, fwd.ids.len(), 64);
    let out = simulate(&fwd, &data, &format!("{label}-fwd"));
    let back = simulate(&inv, &out, &format!("{label}-inv"));
    for (i, (b, d)) in back.iter().zip(&data).enumerate() {
        assert_eq!(b, d, "{label}: garbage inverse shot {i} (W_B {w_b} lo_B {lo_b})");
    }
    cnt.garbage_rt += data.len();
    cnt.inverse_checked += data.len();
}

/// Snapshot of the process environment; `restore` puts it back exactly
/// (removes variables added since, resets changed ones).
struct EnvSnapshot(Vec<(std::ffi::OsString, std::ffi::OsString)>);

impl EnvSnapshot {
    fn take() -> Self {
        Self(std::env::vars_os().collect())
    }
    fn restore(&self) {
        for (k, _) in std::env::vars_os() {
            if !self.0.iter().any(|(sk, _)| *sk == k) {
                std::env::remove_var(&k);
            }
        }
        for (k, v) in &self.0 {
            std::env::set_var(k, v);
        }
    }
}

/// The synthetic D11 rows for one `(W_A, lo_B)` configuration (see the module
/// doc): every combination of `e_B` in a corner set, `off`, `s` (0, 1, 5, the
/// maximum `W_A - E` = the `e_A = W_A` class), `d` in 1..=31+off plus the
/// `32 + off` miss row, half of them dense / tightly packed.
fn synth_div_rows(rng: &mut impl XofReader, w_a: usize, lo_b: usize) -> Vec<DivRow> {
    let (_l, _s_ring, n_w) = top_geometry(w_a, lo_b);
    let lo = lo_b.max(1);
    let mut e_bs = vec![lo, lo + 1, (lo + w_a) / 2, w_a - 1, w_a];
    e_bs.retain(|&e| e >= lo && e <= w_a);
    e_bs.sort_unstable();
    e_bs.dedup();
    let mut rows = Vec::new();
    let mut i = 0usize;
    for &e_b in &e_bs {
        for off in [false, true] {
            let e = e_b + usize::from(off);
            if e > w_a {
                continue;
            }
            let s_max = w_a - e;
            let mut ss = vec![0usize, 1, 5, s_max];
            ss.retain(|&s| s <= s_max);
            ss.sort_unstable();
            ss.dedup();
            for &s in &ss {
                let ea_old = e + s;
                let mut ds: Vec<usize> = (1..=n_w - 1 + usize::from(off)).collect();
                ds.push(n_w + usize::from(off)); // the miss row
                for &d in &ds {
                    if d > ea_old - 1 {
                        break; // bl(A_new) >= 1
                    }
                    i += 1;
                    let dense = i % 2 == 0;
                    // tight packing on dense rows (R1 gap 0), a random narrower
                    // cb otherwise (bl >= 1)
                    let cb_max = RING - ea_old;
                    let cb_bl = if dense { cb_max } else { 1 + rnd_below(rng, U512::from(cb_max as u64)).as_limbs()[0] as usize };
                    let step = if d > n_w - 1 + usize::from(off) { SYNTH_MISS } else { SYNTH };
                    if let Some(row) = synth_div(rng, e_b, off, s, d, cb_bl, dense, step) {
                        rows.push(row);
                    }
                }
            }
        }
    }
    // empty-field rows (R = 0): need L = 0 and e_B <= 31 so the wrapped MSB
    // lands in the window; off = 0, d in [E, E + s - 1] with d <= n_w - 1
    if lo_b <= WINDOW {
        for &e_b in &[lo, lo + 1, 3, 7, 17, 31] {
            if e_b < lo || e_b > w_a || e_b >= WINDOW {
                continue;
            }
            for &s in &[1usize, 2, 5, 20, w_a - e_b] {
                if s == 0 || e_b + s > w_a {
                    continue;
                }
                for &d in &[e_b, e_b + 1, e_b + s - 1, (n_w - 1).min(e_b + s - 1)] {
                    if d < e_b || d > e_b + s - 1 || d > n_w - 1 {
                        continue;
                    }
                    i += 1;
                    let dense = i % 2 == 0;
                    let cb_bl = RING - (e_b + s);
                    if let Some(row) = synth_div(rng, e_b, false, s, d, cb_bl, dense, SYNTH) {
                        rows.push(row);
                    }
                }
            }
        }
    }
    rows
}

/// The synthetic M1 rows for one `(W_B, lo_B)` configuration: `e_B` corners
/// (lo_B, lo_B + 1, mid, W_B - 1, W_B), gaps {0, 1, 2, 24, 25, 30, 31} and
/// `ca_old = 0`, with B random / all ones / a single MSB.
fn synth_mul_rows(rng: &mut impl XofReader, w_b: usize, lo_b: usize) -> Vec<MulRow> {
    let lo = lo_b.max(1);
    let mut e_bs = vec![lo, lo + 1, (lo + w_b) / 2, w_b - 1, w_b, 225, 226, 255, 256];
    e_bs.retain(|&e| e >= lo && e <= w_b);
    e_bs.sort_unstable();
    e_bs.dedup();
    let mut rows = Vec::new();
    let mut i = 0usize;
    for &e_b in &e_bs {
        for b_kind in 0..3u8 {
            for gap in [None, Some(0), Some(1), Some(2), Some(24), Some(25), Some(30), Some(31)] {
                i += 1;
                if let Some(row) = synth_mul(rng, e_b, gap, b_kind, i % 2 == 0) {
                    rows.push(row);
                }
            }
        }
    }
    rows
}

/// One natural step at `(w_a, lo_b)`: the D11 batch (division rows gate = 1,
/// other rows as fillers) and the M1 batch (multiply rows, fillers) as in the
/// main loop. Returns (T_D11, T_M1, circuits).
fn natural_step(traces: &[Trace], step: usize, w_a: usize, lo_b: usize, label: &str, cnt: &mut Counts) -> (usize, usize, usize) {
    let mut shots = Vec::new();
    let mut wit = Vec::new();
    for t in traces {
        match &t.div[step] {
            Some(row) if bl(&row.a_old) <= w_a && lo_b <= bl(&row.b) && bl(&row.b) <= w_a => {
                shots.push(top_shot(row, w_a, lo_b, true, false, cnt));
                wit.push(true);
            }
            _ => {
                shots.push(top_filler(&t.pre[step], cnt));
                wit.push(false);
            }
        }
    }
    let t_top = round_trip_top(w_a, lo_b, &shots, &wit, &format!("{label}-top-s{step}"), cnt);
    let (w_b, lo_m) = (w_a.min(256), lo_b.min(225));
    let mut shots = Vec::new();
    for t in traces {
        match &t.mul[step] {
            Some(row) if lo_m <= bl(&row.b) && bl(&row.b) <= w_b => shots.push(bottom_shot(row, w_b, lo_m, true, cnt)),
            _ => shots.push(bottom_filler(&t.pre[step], cnt)),
        }
    }
    let t_bot = round_trip_bottom(w_b, lo_m, &shots, &format!("{label}-bot-s{step}"), cnt);
    (t_top, t_bot, 4)
}

fn random_inputs() -> Vec<U512> {
    let mut seed = Shake256::default();
    seed.update(b"packed-aligned-scan-inputs-v1");
    let mut xof = seed.finalize_xof();
    let p = p();
    (0..NINPUTS)
        .map(|_| {
            let mut bytes = [0u8; 64];
            xof.read(&mut bytes[..32]);
            let x = U512::from_le_bytes(bytes) % p;
            if x.is_zero() { U512::from(1u64) } else { x }
        })
        .collect()
}

pub(super) fn run() {
    let prev_zero = std::env::var("MIDQ_KG_ZERO_LAYER").ok();
    std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");
    let inputs = random_inputs();
    let traces: Vec<Trace> = inputs.iter().map(|&x| trace(x)).collect();
    // sample envelope per step (record_sample-style): W = max(bl A, bl B), lo = min bl B
    let env_a: Vec<usize> = (0..NSTEPS)
        .map(|i| traces.iter().map(|t| bl(&t.pre[i].a).max(bl(&t.pre[i].b))).max().unwrap())
        .collect();
    let lo_min: Vec<usize> = (0..NSTEPS)
        .map(|i| traces.iter().map(|t| bl(&t.pre[i].b)).min().unwrap())
        .collect();
    let mut cnt = Counts::default();
    let steps = [0usize, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 200, 233, 300, 350, 377, 400, 430, 460, 480, 500, 510, 520, 529];
    let mut t_rows: Vec<String> = Vec::new();
    let mut circuits = 0usize;

    // ---- per-step batches: D11 and M1 at the sample envelope -----------------
    for &step in &steps {
        let w = env_a[step].max(1);
        let lo_thin = w.saturating_sub(78);
        let mut top_cfgs = vec![(w, lo_min[step]), (w, lo_thin)];
        let wide = (w + 20).min(256);
        if wide != w { top_cfgs.push((wide, lo_min[step].min(wide))); }
        for (ci, &(w_a, lo_b)) in top_cfgs.iter().enumerate() {
            if w_a - lo_b >= 128 { continue; }
            let mut shots = Vec::new();
            let mut wit = Vec::new();
            for t in &traces {
                match &t.div[step] {
                    Some(row) if bl(&row.a_old) <= w_a && lo_b <= bl(&row.b) && bl(&row.b) <= w_a => {
                        shots.push(top_shot(row, w_a, lo_b, true, false, &mut cnt));
                        wit.push(true);
                    }
                    _ => {
                        shots.push(top_filler(&t.pre[step], &mut cnt));
                        wit.push(false);
                    }
                }
            }
            let t = round_trip_top(w_a, lo_b, &shots, &wit, &format!("top-s{step}-c{ci}"), &mut cnt);
            circuits += 2;
            // the same division rows with gate = 0
            let mut shots0 = Vec::new();
            for t in &traces {
                if let Some(row) = &t.div[step] {
                    if bl(&row.a_old) <= w_a && lo_b <= bl(&row.b) && bl(&row.b) <= w_a {
                        shots0.push(top_shot(row, w_a, lo_b, false, false, &mut cnt));
                    }
                }
            }
            if !shots0.is_empty() {
                let wit0 = vec![true; shots0.len()];
                round_trip_top(w_a, lo_b, &shots0, &wit0, &format!("top0-s{step}-c{ci}"), &mut cnt);
                circuits += 2;
            }
            if ci == 0 {
                let (l, s_ring, n_w) = top_geometry(w_a, lo_b);
                t_rows.push(format!("D11 step {step:3} W_A {w_a:3} lo_B {lo_b:3} L {l:3} S {s_ring:3} n_w {n_w:2}: T {t:5} (rot {})", 2 * subring_rotate_toffoli(s_ring, T7_BITS)));
            }
        }
        let w_b = w.min(256);
        let bot_cfgs = [(w_b, lo_min[step].min(225)), (w_b, lo_thin.min(225))];
        for (ci, &(w_b, lo_b)) in bot_cfgs.iter().enumerate() {
            if w_b < lo_b || w_b - lo_b >= 128 { continue; }
            let mut shots = Vec::new();
            for t in &traces {
                match &t.mul[step] {
                    Some(row) if lo_b <= bl(&row.b) && bl(&row.b) <= w_b => {
                        shots.push(bottom_shot(row, w_b, lo_b, true, &mut cnt));
                    }
                    _ => shots.push(bottom_filler(&t.pre[step], &mut cnt)),
                }
            }
            let t = round_trip_bottom(w_b, lo_b, &shots, &format!("bot-s{step}-c{ci}"), &mut cnt);
            circuits += 2;
            let mut shots0 = Vec::new();
            for t in &traces {
                if let Some(row) = &t.mul[step] {
                    if lo_b <= bl(&row.b) && bl(&row.b) <= w_b {
                        shots0.push(bottom_shot(row, w_b, lo_b, false, &mut cnt));
                    }
                }
            }
            if !shots0.is_empty() {
                round_trip_bottom(w_b, lo_b, &shots0, &format!("bot0-s{step}-c{ci}"), &mut cnt);
                circuits += 2;
            }
            if ci == 0 {
                let (top, s_ring) = bottom_geometry(w_b, lo_b);
                t_rows.push(format!("M1  step {step:3} W_B {w_b:3} lo_B {lo_b:3} T {top:3} S {s_ring:3}      : T {t:5} (rot {})", 2 * subring_rotate_toffoli(s_ring, T7_BITS)));
            }
        }
    }

    // ---- first multiplies (ca_old = 0): e_B in [226,256] wraps B's bits ------
    let firsts: Vec<MulRow> = traces
        .iter()
        .filter_map(|t| t.mul.iter().flatten().find(|r| r.ca_old.is_zero()).cloned())
        .collect();
    assert_eq!(firsts.len(), NINPUTS, "every input has a first multiply");
    for &(w_b, lo_b) in &[(256usize, 190usize), (256, 225), (255, 178)] {
        let rows: Vec<&MulRow> = firsts.iter().filter(|r| lo_b <= bl(&r.b) && bl(&r.b) <= w_b).collect();
        if rows.is_empty() { continue; }
        let shots: Vec<BotShot> = rows.iter().map(|r| bottom_shot(r, w_b, lo_b, true, &mut cnt)).collect();
        round_trip_bottom(w_b, lo_b, &shots, &format!("first-{w_b}-{lo_b}"), &mut cnt);
        circuits += 2;
    }

    // ---- synthetic M1 rows: every gap in [0, 31] and ca_old = 0 across e_B in
    // [1, 256] (the natural sample never has a first multiply with e_B <= 225:
    // bl(x) >= 226 with probability 1 - 2^-30, so the all-zero window and the
    // e_B = 256 corner are synthesised; B and ca are random with the given widths)
    let mut synth_seed = Shake256::default();
    synth_seed.update(b"packed-aligned-scan-synthetic-v1");
    let mut synth = synth_seed.finalize_xof();
    let mut rand_width = |w: usize| -> U512 {
        if w == 0 { return U512::ZERO; }
        let mut bytes = [0u8; 64];
        synth.read(&mut bytes[..33]);
        let mask = (U512::from(1u64) << w) - U512::from(1u64);
        (U512::from_le_bytes(bytes) & mask) | (U512::from(1u64) << (w - 1))
    };
    let e_bs = [1usize, 2, 3, 31, 32, 33, 63, 64, 65, 100, 177, 178, 179, 200, 224, 225, 226, 227, 240, 250, 254, 255, 256];
    let gaps = [0usize, 1, 2, 3, 5, 8, 13, 21, 24, 25, 26, 30, 31];
    let mut synth_rows: Vec<MulRow> = Vec::new();
    for &e_b in &e_bs {
        let b = rand_width(e_b);
        synth_rows.push(MulRow { step: usize::MAX, a: U512::from(1u64), b, ca_old: U512::ZERO });
        for &g in &gaps {
            if g + e_b + 1 <= RING {
                let ca = rand_width(RING - e_b - g);
                synth_rows.push(MulRow { step: usize::MAX, a: U512::from(1u64), b, ca_old: ca });
            }
        }
    }
    let synth_cfgs = [(256usize, 178usize), (177, 64), (63, 1)];
    let mut synthetic = 0usize;
    for &(w_b, lo_b) in &synth_cfgs {
        let rows: Vec<&MulRow> = synth_rows.iter().filter(|r| lo_b <= bl(&r.b) && bl(&r.b) <= w_b).collect();
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<BotShot> = chunk.iter().map(|r| bottom_shot(r, w_b, lo_b, true, &mut cnt)).collect();
            round_trip_bottom(w_b, lo_b, &shots, &format!("synth-{w_b}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
            synthetic += chunk.len();
        }
    }

    // ---- draining multiplies (A = 0, B = 1, q != 0) --------------------------
    let drains: Vec<MulRow> = traces
        .iter()
        .flat_map(|t| t.mul.iter().flatten().filter(|r| r.a.is_zero()).cloned())
        .take(64)
        .collect();
    if !drains.is_empty() {
        let shots: Vec<BotShot> = drains.iter().map(|r| bottom_shot(r, 8, 1, true, &mut cnt)).collect();
        round_trip_bottom(8, 1, &shots, "drain", &mut cnt);
        circuits += 2;
    }

    // ---- terminal divisions (A_new = 0): garbage k, plus synthetic all-zero windows
    let terms: Vec<DivRow> = traces
        .iter()
        .filter_map(|t| t.div.iter().flatten().find(|r| r.a_new.is_zero()).cloned())
        .collect();
    assert_eq!(terms.len(), NINPUTS, "every input has a terminal division");
    let w_term = terms.iter().map(|r| bl(&r.a_old)).max().unwrap().max(2);
    for zero_cb in [false, true] {
        let shots: Vec<TopShot> = terms.iter().map(|r| top_shot(r, w_term, 1, true, zero_cb, &mut cnt)).collect();
        let wit = vec![true; shots.len()];
        round_trip_top(w_term, 1, &shots, &wit, &format!("term-{zero_cb}"), &mut cnt);
        circuits += 2;
    }
    // the same terminal rows with a 32+ ring (W_A = 40, lo_B = 1: L = 0, wrap)
    for zero_cb in [false, true] {
        let shots: Vec<TopShot> = terms.iter().map(|r| top_shot(r, 40, 1, true, zero_cb, &mut cnt)).collect();
        let wit = vec![true; shots.len()];
        round_trip_top(40, 1, &shots, &wit, &format!("term40-{zero_cb}"), &mut cnt);
        circuits += 2;
    }

    // ---- division rows with R1 gap 0 / e_B < 32 at a wide ring (L = 0 wrap) ---
    let mut wrap_rows: Vec<DivRow> = traces
        .iter()
        .flat_map(|t| t.div.iter().flatten().filter(|r| bl(&r.b) < WINDOW && !r.a_new.is_zero()).cloned())
        .collect();
    wrap_rows.truncate(64);
    if !wrap_rows.is_empty() {
        let w_a = wrap_rows.iter().map(|r| bl(&r.a_old)).max().unwrap().max(WINDOW + 8);
        let shots: Vec<TopShot> = wrap_rows.iter().map(|r| top_shot(r, w_a, 1, true, false, &mut cnt)).collect();
        let wit = vec![true; shots.len()];
        round_trip_top(w_a, 1, &shots, &wit, "wrap", &mut cnt);
        circuits += 2;
    }

    // =====================================================================
    // Review additions (adversarial classes the natural sample cannot reach).
    // =====================================================================
    let mut rev_seed = Shake256::default();
    rev_seed.update(b"packed-aligned-scan-review-v1");
    let mut rev = rev_seed.finalize_xof();

    // ---- synthetic D11 rows: d = 1..31+off (MSB at every window index), the
    // 32+off miss row, tight packing / dense foreign bits, empty field (R = 0),
    // e_A = W_A & off = 0, e_B = lo_B (t7 = 127 on the 159-ring) and e_B = W_A
    // (t7 = 0), rings 127/128/64/33/32/31/24/16 (L = 0, skipped layers), L = 1
    let top_synth_cfgs = [
        (256usize, 129usize), (256, 225), (127, 1), (128, 1), (64, 33), (33, 1), (32, 1), (31, 1), (24, 0), (16, 1),
    ];
    let mut synth_top_rows = 0usize;
    for &(w_a, lo_b) in &top_synth_cfgs {
        let rows = synth_div_rows(&mut rev, w_a, lo_b);
        assert!(!rows.is_empty());
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<TopShot> = chunk.iter().map(|r| top_shot(r, w_a, lo_b, true, false, &mut cnt)).collect();
            let wit = vec![true; shots.len()];
            round_trip_top(w_a, lo_b, &shots, &wit, &format!("synthtop-{w_a}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
        }
        synth_top_rows += rows.len();
    }

    // ---- synthetic M1 rows: t7 = 127 / 0, W_B - lo_B = 127, e_B corners incl.
    // 225/226/255/256, B all ones (wrap boundary g = 257 - e_B) and B = 2^(e_B-1)
    let bot_synth_cfgs = [(256usize, 129usize), (256, 225), (128, 1), (200, 100), (64, 33), (32, 1), (1, 1)];
    let mut synth_bot_rows = 0usize;
    for &(w_b, lo_b) in &bot_synth_cfgs {
        let rows = synth_mul_rows(&mut rev, w_b, lo_b);
        assert!(!rows.is_empty());
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<BotShot> = chunk.iter().map(|r| bottom_shot(r, w_b, lo_b, true, &mut cnt)).collect();
            round_trip_bottom(w_b, lo_b, &shots, &format!("synthbot-{w_b}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
        }
        synth_bot_rows += rows.len();
    }

    // ---- random garbage rows: exact inverse for ANY input (gate 0/1,
    // exponents 0..511 incl. e_B = 0 / e_B < lo_B / e_B > W, any ring content)
    for &(w_a, lo_b) in &[(256usize, 129usize), (256, 225), (110, 1), (64, 33), (32, 1), (24, 0), (1, 1)] {
        garbage_top(w_a, lo_b, &mut rev, &format!("garbtop-{w_a}-{lo_b}"), &mut cnt);
        circuits += 2;
    }
    for &(w_b, lo_b) in &[(256usize, 129usize), (256, 225), (128, 1), (24, 0), (1, 1)] {
        garbage_bottom(w_b, lo_b, &mut rev, &format!("garbbot-{w_b}-{lo_b}"), &mut cnt);
        circuits += 2;
    }

    // ---- D11 without the k = -1 layer: the frame claims hold without it; an
    // all-zero window then deposits 0 (the classical model follows `sentinel()`)
    std::env::remove_var("MIDQ_KG_ZERO_LAYER");
    assert!(!kg_zero_layer_enabled());
    for zero_cb in [false, true] {
        let shots: Vec<TopShot> = terms.iter().map(|r| top_shot(r, 40, 1, true, zero_cb, &mut cnt)).collect();
        let wit = vec![true; shots.len()];
        round_trip_top(40, 1, &shots, &wit, &format!("nozero-term40-{zero_cb}"), &mut cnt);
        circuits += 2;
        cnt.zero_layer_off += shots.len();
    }
    for &(w_a, lo_b) in &[(64usize, 33usize), (33, 1)] {
        let rows = synth_div_rows(&mut rev, w_a, lo_b);
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<TopShot> = chunk.iter().map(|r| top_shot(r, w_a, lo_b, true, false, &mut cnt)).collect();
            let wit = vec![true; shots.len()];
            round_trip_top(w_a, lo_b, &shots, &wit, &format!("nozero-synth-{w_a}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
            cnt.zero_layer_off += chunk.len();
        }
    }
    std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");

    // ---- the production route (configure_sub1000_trailmix_route: LOWQ_ONE_A_ELIM,
    // LOWQ_COMPACT_KGANC, MIDQ_CHUNK_COMPARE + MIDQ_VARIABLE_CHUNKS, ...) with
    // MIDQ_CHUNKED_PREFIX forced off (its default "1" has no k = -1 layer and
    // is refused by aligned_scan). Natural mid/late steps, the synthetic D11 /
    // M1 sets, first multiplies, terminal and draining rows; T under the route.
    let snapshot = EnvSnapshot::take();
    let pre_route_chunk_compare = std::env::var_os("MIDQ_CHUNK_COMPARE");
    let pre_route_chunked_prefix = std::env::var_os("MIDQ_CHUNKED_PREFIX");
    std::env::set_var("MIDQ_CHUNKED_PREFIX", "0");
    std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");
    crate::point_add::trailmix_port::configure_sub1000_trailmix_route();
    assert!(kg_zero_layer_enabled());
    assert_eq!(std::env::var("LOWQ_ONE_A_ELIM").ok().as_deref(), Some("1"));
    assert_eq!(std::env::var("MIDQ_CHUNK_COMPARE").ok().as_deref(), Some("1"));
    let mut route_rows: Vec<String> = Vec::new();
    for &step in &[89usize, 300, 377, 430, 480] {
        let w = env_a[step].max(1);
        let lo_b = lo_min[step];
        let (tt, tb, c) = natural_step(&traces, step, w, lo_b, "route", &mut cnt);
        circuits += c;
        cnt.route_rt += 2 * NINPUTS;
        route_rows.push(format!("route step {step:3} W {w:3} lo_B {lo_b:3}: D11 T {tt:5} | M1 T {tb:5}"));
    }
    for &(w_a, lo_b) in &[(256usize, 129usize), (33, 1)] {
        let rows = synth_div_rows(&mut rev, w_a, lo_b);
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<TopShot> = chunk.iter().map(|r| top_shot(r, w_a, lo_b, true, false, &mut cnt)).collect();
            let wit = vec![true; shots.len()];
            round_trip_top(w_a, lo_b, &shots, &wit, &format!("route-synthtop-{w_a}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
            cnt.route_rt += chunk.len();
        }
    }
    for &(w_b, lo_b) in &[(256usize, 129usize), (256, 225), (32, 1)] {
        let rows = synth_mul_rows(&mut rev, w_b, lo_b);
        for (bi, chunk) in rows.chunks(64).enumerate() {
            let shots: Vec<BotShot> = chunk.iter().map(|r| bottom_shot(r, w_b, lo_b, true, &mut cnt)).collect();
            round_trip_bottom(w_b, lo_b, &shots, &format!("route-synthbot-{w_b}-{lo_b}-{bi}"), &mut cnt);
            circuits += 2;
            cnt.route_rt += chunk.len();
        }
    }
    {
        let rows: Vec<&MulRow> = firsts.iter().filter(|r| 225 <= bl(&r.b) && bl(&r.b) <= 256).collect();
        let shots: Vec<BotShot> = rows.iter().map(|r| bottom_shot(r, 256, 225, true, &mut cnt)).collect();
        round_trip_bottom(256, 225, &shots, "route-first", &mut cnt);
        circuits += 2;
        cnt.route_rt += shots.len();
        for zero_cb in [false, true] {
            let shots: Vec<TopShot> = terms.iter().map(|r| top_shot(r, w_term, 1, true, zero_cb, &mut cnt)).collect();
            let wit = vec![true; shots.len()];
            round_trip_top(w_term, 1, &shots, &wit, &format!("route-term-{zero_cb}"), &mut cnt);
            circuits += 2;
            cnt.route_rt += shots.len();
        }
        if !drains.is_empty() {
            let shots: Vec<BotShot> = drains.iter().map(|r| bottom_shot(r, 8, 1, true, &mut cnt)).collect();
            round_trip_bottom(8, 1, &shots, "route-drain", &mut cnt);
            circuits += 2;
            cnt.route_rt += shots.len();
        }
        garbage_top(256, 129, &mut rev, "route-garbtop", &mut cnt);
        garbage_bottom(256, 129, &mut rev, "route-garbbot", &mut cnt);
        circuits += 4;
    }
    for &(step, w_a) in &[(300usize, 117usize), (378, 76)] {
        let lo_b = w_a.saturating_sub(78);
        let top_h = build_top(w_a, lo_b, false);
        let bot_h = build_bottom(w_a.min(256), lo_b.min(225), false);
        route_rows.push(format!(
            "route design step {step} W_A {w_a} lo_B {lo_b}: D11 T {} (peak scratch {}) | M1 T {} (peak scratch {})",
            top_h.t, top_h.scratch, bot_h.t, bot_h.scratch
        ));
    }
    snapshot.restore();
    // the route's defaults must not leak into the following selftests
    assert_eq!(std::env::var_os("MIDQ_CHUNK_COMPARE"), pre_route_chunk_compare);
    assert_eq!(std::env::var_os("MIDQ_CHUNKED_PREFIX"), pre_route_chunked_prefix);
    assert!(kg_zero_layer_enabled());

    // ---- design-table configurations (count only): T at the section-4 steps ---
    let design = [(0usize, 256usize), (100, 215), (200, 167), (300, 117), (378, 76), (400, 66), (440, 44), (480, 24), (500, 12), (529, 1)];
    let mut design_rows = Vec::new();
    for &(step, w_a) in &design {
        let lo_b = w_a.saturating_sub(78);
        let top_h = build_top(w_a, lo_b, false);
        let top = top_h.t;
        let (l, s_top, n_w) = top_geometry(w_a, lo_b);
        let lo_m1 = lo_b.min(225);
        let bot_h = build_bottom(w_a.min(256), lo_m1, false);
        let bot = bot_h.t;
        let (_t, s_bot) = bottom_geometry(w_a.min(256), lo_m1);
        design_rows.push(format!(
            "step {step:3} W_A {w_a:3} lo_B {lo_b:3}: D11 T {top:5} (ring [{l},{w_a}) S {s_top:3} n_w {n_w:2}, rot {:4}, scan+arith {:4}, peak scratch {}) | M1 T {bot:5} (S {s_bot:3}, rot {:4}, scan+arith {:4}, peak scratch {})",
            2 * subring_rotate_toffoli(s_top, T7_BITS), top - 2 * subring_rotate_toffoli(s_top, T7_BITS), top_h.scratch,
            2 * subring_rotate_toffoli(s_bot, T7_BITS), bot - 2 * subring_rotate_toffoli(s_bot, T7_BITS), bot_h.scratch));
    }

    // ---- unit pieces (count only) ---------------------------------------------
    let piece = |name: &str, f: &dyn Fn(&mut Circuit)| -> String {
        let mut c = Circuit::new();
        f(&mut c);
        format!("{name} {}", toffoli(&c.b.ops))
    };
    let pieces = [
        piece("t7(7b)", &|c| {
            let t = c.alloc_qreg_bits("t", T7_BITS);
            let e = c.alloc_qreg_bits("e", EXP_BITS);
            exp_offset(c, &t, &e, 76, true, false);
        }),
        piece("ladder32(3n)", &|c| {
            let w = c.alloc_qreg_bits("w", WINDOW);
            let pos = c.alloc_qreg_bits("p", POS_BITS);
            let wr: Vec<&QReg> = w.iter().collect();
            bit_length_lean_middle(c, &wr, &pos, |_| false);
        }),
        piece("narrow_add(6->9,+1)", &|c| {
            let a = c.alloc_qreg_bits("a", EXP_BITS);
            let b = c.alloc_qreg_bits("b", POS_BITS);
            let g = c.alloc_qreg("g");
            let ar: Vec<&QReg> = a.iter().collect();
            let br: Vec<&QReg> = b.iter().collect();
            ctrl_add_narrow(c, &g, &ar, &br, true);
        }),
        piece("narrow_add(5->9)", &|c| {
            let a = c.alloc_qreg_bits("a", EXP_BITS);
            let b = c.alloc_qreg_bits("b", 5);
            let g = c.alloc_qreg("g");
            let ar: Vec<&QReg> = a.iter().collect();
            let br: Vec<&QReg> = b.iter().collect();
            ctrl_add_narrow(c, &g, &ar, &br, false);
        }),
        piece("ctrl_add_const(-32)", &|c| {
            let a = c.alloc_qreg_bits("a", EXP_BITS);
            let g = c.alloc_qreg("g");
            let ar: Vec<&QReg> = a.iter().collect();
            ctrl_add_const(c, &g, &ar, 512 - 32);
        }),
        piece("ctrl_add_const(-24)", &|c| {
            let a = c.alloc_qreg_bits("a", EXP_BITS);
            let g = c.alloc_qreg("g");
            let ar: Vec<&QReg> = a.iter().collect();
            ctrl_add_const(c, &g, &ar, 512 - 24);
        }),
        piece("u=257-e", &|c| {
            let e = c.alloc_qreg_bits("e", EXP_BITS);
            exp_to_257_minus(c, &e, false);
        }),
        piece("cmp9", &|c| {
            let v = c.alloc_qreg_bits("v", EXP_BITS);
            let u = c.alloc_qreg_bits("u", EXP_BITS);
            let o = c.alloc_qreg("o");
            let vr: Vec<&QReg> = v.iter().collect();
            let ur: Vec<&QReg> = u.iter().collect();
            borrow_compare_refs(c, &vr, &ur, &o);
        }),
        piece("ctrl_add9", &|c| {
            let a = c.alloc_qreg_bits("a", EXP_BITS);
            let b = c.alloc_qreg_bits("b", EXP_BITS);
            let g = c.alloc_qreg("g");
            let ar: Vec<&QReg> = a.iter().collect();
            let br: Vec<&QReg> = b.iter().collect();
            ctrl_add_full(c, &g, &ar, &br);
        }),
    ];

    // ---- required classes -------------------------------------------------------
    assert!(cnt.div_support > 0 && cnt.mul_support > 0);
    assert!(cnt.gap1_zero > 0, "no R1 gap = 0 rows");
    assert!(cnt.ea_eq_wa_off0 > 0, "no e_A = W_A, off = 0 rows");
    assert!(cnt.eb_lt_32 > 0, "no e_B < 32 rows");
    assert!(cnt.foreign_below > 0, "no foreign-bits-below-MSB rows");
    assert!(cnt.wa_lt_32 > 0, "no W_A < 32 rows");
    assert!(cnt.terminal > 0 && cnt.allzero_win > 0);
    assert!(cnt.first_mul_hi_eb > 0, "no first multiply with e_B >= 226");
    assert!(cnt.first_mul_lo_eb > 0, "no first multiply with e_B <= 225 (all-zero window)");
    assert!(cnt.draining > 0, "no draining rows");
    assert!(cnt.off1 > 0 && cnt.gate0 > 0);
    assert_eq!(cnt.drop_bound_miss, 0, "drop_bound miss in the sample");
    assert_eq!(cnt.gap_bound_miss, 0, "gap_bound miss in the sample");
    // review classes
    assert!(cnt.synth_div > 0 && cnt.synth_div_miss > 0, "synthetic D11 rows");
    assert_eq!(cnt.synth_d_max, WINDOW, "d = 31 + off with off = 1 must be reached");
    assert!(cnt.k_top > 0 && cnt.k_zero > 0, "MSB at the window top / bottom");
    assert!(cnt.empty_field > 0, "empty-field rows (R = 0)");
    assert!(cnt.t7_zero_top > 0 && cnt.t7_max_top > 0, "D11 t7 = 0 / 127");
    assert!(cnt.ring_gt_128_top > 0 && cnt.ring_pow2_top > 0, "D11 rings > 128 and power-of-two");
    assert!(cnt.synth_ea_eq_wa_off0 > 0 && cnt.synth_gap1_zero > 0);
    assert!(cnt.t7_zero_bot > 0 && cnt.t7_max_bot > 0, "M1 t7 = 0 / 127");
    assert!(cnt.nz_boundary > 0 && cnt.b_all_ones_wrap > 0, "nz boundary g = 257 - e_B");
    assert!(cnt.garbage_rt > 0 && cnt.zero_layer_off > 0 && cnt.route_rt > 0);

    for r in &t_rows { eprintln!("PACKED_ALIGNED_SCAN {r}"); }
    for r in &design_rows { eprintln!("PACKED_ALIGNED_SCAN design {r}"); }
    for r in &route_rows { eprintln!("PACKED_ALIGNED_SCAN {r}"); }
    eprintln!("PACKED_ALIGNED_SCAN pieces: {}", pieces.join(" | "));
    eprintln!(
        "PACKED_ALIGNED_SCAN review: synthetic D11 rows {} (support {}, drop_bound-miss rows {} [sentinel asserted], d_max {}, \
         k = n_w-1 {}, k = 0 {}, empty field {}, t7 = 0 {}, t7 = 127 {}, ring > 128 {}, ring 2^k {}, e_A = W_A & off = 0 {}, gap1 = 0 {}), \
         synthetic M1 rows {} (t7 = 0 {}, t7 = 127 {}, nz boundary g = 257 - e_B {}, B all-ones wrap {}), \
         garbage round trips {}, D11 rows without the zero layer {}, production-route rows {}",
        synth_top_rows, cnt.synth_div, cnt.synth_div_miss, cnt.synth_d_max,
        cnt.k_top, cnt.k_zero, cnt.empty_field, cnt.t7_zero_top, cnt.t7_max_top, cnt.ring_gt_128_top, cnt.ring_pow2_top,
        cnt.synth_ea_eq_wa_off0, cnt.synth_gap1_zero,
        synth_bot_rows, cnt.t7_zero_bot, cnt.t7_max_bot, cnt.nz_boundary, cnt.b_all_ones_wrap,
        cnt.garbage_rt, cnt.zero_layer_off, cnt.route_rt
    );
    eprintln!(
        "PACKED_ALIGNED_SCAN selftest PASS: {} inputs x {} steps (pz_prefix in U512), {} circuits, \
         D11 rows {} (support {}, gap1=0 {}, e_A=W_A&off=0 {}, e_B<32 {}, foreign-below {}, W_A<32 {}, off=1 {}, \
         terminal {}, all-zero windows {}, d_max {}, drop_bound misses {}), \
         M1 rows {} (support {}, first-mul {} [e_B>=226: {}, e_B<=225: {}], draining {}, natural gap2_max {}, gap_bound misses {}), \
         synthetic M1 rows {} (gaps 0..{}, e_B 1..256, ca_old = 0 incl. e_B <= 225), \
         gate=0 rows {}, forward+inverse round trips {}; phase 0, ancillae clean at every reset",
        NINPUTS, NSTEPS, circuits,
        cnt.div_rows, cnt.div_support, cnt.gap1_zero, cnt.ea_eq_wa_off0, cnt.eb_lt_32, cnt.foreign_below, cnt.wa_lt_32, cnt.off1,
        cnt.terminal, cnt.allzero_win, cnt.d_max, cnt.drop_bound_miss,
        cnt.mul_rows, cnt.mul_support, cnt.first_mul, cnt.first_mul_hi_eb, cnt.first_mul_lo_eb, cnt.draining, cnt.gap2_max, cnt.gap_bound_miss,
        synthetic, cnt.gap2_synth_max, cnt.gate0, cnt.inverse_checked
    );
    match prev_zero {
        Some(v) => std::env::set_var("MIDQ_KG_ZERO_LAYER", v),
        None => std::env::remove_var("MIDQ_KG_ZERO_LAYER"),
    }
}
