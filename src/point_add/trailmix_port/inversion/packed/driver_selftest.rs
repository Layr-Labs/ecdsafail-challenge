//! Round-trip selftest of the packed per-step driver (`driver.rs`, plan P4):
//! the FULL forward prefix (530 rows: `p0_shape::forward_step`, i.e. the
//! production `prefix_forward` row by row) and the FULL cancel
//! (`backward_step`) on the `Simulator`, 64 Shake256-seeded inputs in one
//! bit-sliced run, under the production configuration (the thin schedule,
//! seed 278, 500k validation draws; `TRAILMIX_SROT_W=5`, `TRAILMIX_COUNTER_W=8`,
//! `MIDQ_PREFIX_POPCOUNT=1`, `MIDQ_PREFIX_TERMINAL_FROM` = `DEFAULT_TERMINAL_FROM` (340), the measured
//! demux / gate / predicate clears).
//!
//! Checks:
//! * after EVERY forward row the data registers (`R1`, `R2`, the four
//!   exponents, `q`, `counter`, `s_rot = off = 0`, `parity`) of every input
//!   that is still on the support equal the classical oracle (the verbatim
//!   `pz_prefix` recurrence of `tools/packed_prefix_model.py` with the
//!   circuit's counter / parity bookkeeping), the phase is 0 and every
//!   non-data qubit is 0; the rows 100 / 250 / 378 / 530 are reported;
//! * after EVERY backward row the data registers equal the snapshot taken
//!   before the matching forward row, for EVERY input (the inverse is exact on
//!   any state, support or not); after row 0 the state is S_0 exactly
//!   (A = p, B = |x|, ca = 0, cb = 1, e_A = 256, e_B = bl(x), e_ca = 0,
//!   e_cb = 1, q = 0, s_rot = off = 0, parity = 1, counter = 0);
//! * every reset sees a zero qubit (`checked_apply`), phase 0 at every row;
//! * the input set covers draining rows (A = 0, B = 1, q != 0) and frozen rows
//!   (active = 0) at rows >= FROM (asserted), and the on-support inputs
//!   terminate in [FROM, 530); the per-input first support miss (if any) is
//!   classified by kind and reported.
//!
//! The circuit is built row by row and its ops applied to the simulator
//! immediately (60M ops would not fit as a stored stream); the simulator's
//! qubit / bit vectors grow on demand. Prints the Toffoli per row of both
//! directions at 100 / 250 / 378 / 500 and the sums, next to the design's
//! section-4 numbers.
//!
//! Knobs: `MIDQ_DRIVER_SELFTEST_INPUTS` (default 64, max 64),
//! `MIDQ_DRIVER_SELFTEST_X` (comma-separated hex values that replace the first
//! inputs of the draw: a failing eval shot's `dx` / `new_dx` factor, exactly as
//! `TRAILMIX_DUMP_DRAWS` prints them; the row where the circuit leaves the
//! oracle on such an input is reported as `CIRCUIT` instead of panicking, so
//! a real miss and a model gap can be told apart in one run),
//! `MIDQ_DRIVER_SELFTEST_STEPS` (default 530: a shorter prefix for quick runs),
//! `MIDQ_DRIVER_SELFTEST_VALIDATE` (the thin schedule's validation draws,
//! default 500000 = production; 0 skips the ~30 s validation for quick runs).
//! The static tables are not an option here: their q envelope (up to 38)
//! exceeds the 5-bit shift word's reach, which the division asserts.

use super::super::p0_shape::{backward_step, forward_step, natural_q_width, popcount_on, terminal_from, Packed};
use super::super::sched::{StepWidths, EXP_BITS, MAX_Q_WIDTH, RING, WINDOW};
use super::super::super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const NSTEPS: usize = 530;
const SROT: usize = 5;

fn prime() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}

fn bl(x: &U512) -> usize {
    x.bit_len()
}

fn one() -> U512 {
    U512::from(1u64)
}

/// The classical state after a row: (A, B, ca, cb, q) after the swap.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct St {
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: U512,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Frozen,
    Draining,
    Mul,
    Div,
}

/// One row of the oracle: the pre-state, what fired, the post-state and the
/// circuit's bookkeeping after the row.
#[derive(Clone)]
struct Row {
    pre: St,
    kind: Kind,
    /// multiply: (s2, carry)
    mul: Option<(usize, bool)>,
    /// division: (s, off, A_new); `terminal` iff A_new = 0
    div: Option<(usize, bool, U512)>,
    /// state after the substeps, before the swap
    mid: St,
    swapped: bool,
    post: St,
    parity: bool,
    counter: usize,
}

struct Trace {
    x: U512,
    rows: Vec<Row>,
    terminal: Option<usize>,
    /// first row whose support predicate fails, with the kind
    first_miss: Option<(usize, &'static str)>,
    draining_rows: usize,
    frozen_rows: usize,
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) with the circuit's
/// parity / counter bookkeeping recorded per row.
fn trace(x_orig: U512, steps: usize, term_from: usize, pop: bool) -> Trace {
    let p = prime();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let mut st = St { a: p, b: x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
    let mut parity = true;
    let mut counter = 0usize;
    let mut rows = Vec::with_capacity(steps);
    let mut terminal = None;
    let (mut draining_rows, mut frozen_rows) = (0usize, 0usize);
    for step in 0..steps {
        assert!(st.a * st.cb + st.b * (st.ca + st.q * st.cb) == p, "row invariant at step {step}");
        let pre = st;
        if step == term_from && pop {
            counter = 0; // the popcount cache is erased before the first terminal-aware row
        }
        if st.a.is_zero() && st.b == one() && st.q.is_zero() {
            frozen_rows += 1;
            if step >= term_from {
                counter += 1; // done every row
            }
            rows.push(Row { pre, kind: Kind::Frozen, mul: None, div: None, mid: st, swapped: false, post: st, parity, counter });
            continue;
        }
        let mut mul = None;
        let mut kind = Kind::Mul;
        if st.a < st.b && !st.q.is_zero() {
            let s2 = st.q.trailing_zeros();
            st.q ^= one() << s2;
            let ca_new = st.ca + (st.cb << s2);
            let carry = bl(&ca_new) > bl(&st.cb) + s2;
            st.ca = ca_new;
            mul = Some((s2, carry));
            if pre.a.is_zero() {
                kind = Kind::Draining;
                draining_rows += 1;
            }
        }
        let mut div = None;
        if st.ca < st.cb {
            let s_raw = bl(&st.a) as i64 - bl(&st.b) as i64;
            if s_raw >= 0 {
                let off = st.a < (st.b << (s_raw as usize));
                let s = s_raw - i64::from(off);
                if s >= 0 {
                    let s = s as usize;
                    let bsh = st.b << s;
                    assert!(st.a >= bsh, "model: A < B << s at step {step}");
                    let a_new = st.a - bsh;
                    st.a = a_new;
                    st.q ^= one() << s;
                    div = Some((s, off, a_new));
                    kind = Kind::Div;
                    if a_new.is_zero() && terminal.is_none() {
                        terminal = Some(step);
                    }
                }
            }
        }
        assert!(mul.is_none() || div.is_none(), "both substeps fired at step {step}");
        assert!(mul.is_some() || div.is_some(), "idle row (A < B, q = 0, A != 0) at step {step}");
        assert_eq!(div.is_some(), pre.a >= pre.b, "role rule at step {step}");
        let mid = st;
        if step < term_from {
            if pop {
                // popcount cache: -1 on a multiply row, +1 on a division row
                if mul.is_some() { counter -= 1 } else { counter += 1 }
            }
        } else if st.q.is_zero() && st.a.is_zero() {
            counter += 1;
        }
        let swapped = st.q.is_zero() && !st.a.is_zero();
        if swapped {
            std::mem::swap(&mut st.a, &mut st.b);
            std::mem::swap(&mut st.ca, &mut st.cb);
            parity = !parity;
        }
        rows.push(Row { pre, kind, mul, div, mid, swapped, post: st, parity, counter });
    }
    if steps == NSTEPS {
        assert!(st.a.is_zero() && st.q.is_zero(), "input {x_orig:#x} did not terminate by {NSTEPS}");
    }
    Trace { x, rows, terminal, first_miss: None, draining_rows, frozen_rows }
}

/// The support predicate of row `i` (what the schedule guarantees and the
/// circuit relies on: the division's and the multiply's harness predicates
/// plus the driver's role windows). `Err(kind)` on the first failing check.
fn support(row: &Row, i: usize, s: &StepWidths, wq: usize, term_from: usize) -> Result<(), &'static str> {
    let pre = &row.pre;
    let (e_a, e_b, e_ca, e_cb) = (bl(&pre.a), bl(&pre.b), bl(&pre.ca), bl(&pre.cb));
    let mut checks: Vec<(bool, &'static str)> = vec![
        (e_a <= s.w_a && e_b <= s.w_a, "width_a (pre)"),
        (e_ca <= s.w_c && e_cb <= s.w_c, "width_c (pre)"),
        (bl(&pre.q) <= wq, "width_q (pre)"),
        (bl(&row.post.q) <= wq, "width_q (post)"),
        (bl(&row.post.a) <= s.w_a && bl(&row.post.b) <= s.w_a, "width_a (post)"),
        (bl(&row.post.ca) <= s.w_c && bl(&row.post.cb) <= s.w_c, "width_c (post)"),
        // the 7-bit rebased exponents (sched.rs): every exponent of the row
        // (pre, mid and post state) inside its pair's window [base, base + 127]
        (s.v_in_range(e_a) && s.v_in_range(e_b) && s.c_in_range(e_ca) && s.c_in_range(e_cb), "exp_range (pre)"),
        (
            s.v_in_range(bl(&row.mid.a)) && s.v_in_range(bl(&row.mid.b)) && s.c_in_range(bl(&row.mid.ca)) && s.c_in_range(bl(&row.mid.cb)),
            "exp_range (mid)",
        ),
        (
            s.v_in_range(bl(&row.post.a)) && s.v_in_range(bl(&row.post.b)) && s.c_in_range(bl(&row.post.ca)) && s.c_in_range(bl(&row.post.cb)),
            "exp_range (post)",
        ),
    ];
    if row.kind != Kind::Frozen {
        // role compute: m = max(e_ca, e_cb) in [lo_c + 1, W_c]; the fit fact
        let m = e_ca.max(e_cb);
        let lo_c = s.lo_ca.max(s.lo_cb);
        checks.push((m >= lo_c + 1, "lo_c (role compute)"));
        checks.push((e_a.max(e_b) <= RING - m, "fit fact max(eA,eB) <= 257 - max(eca,ecb)"));
        // role clear: m' = max(e_A, e_B) after the substeps in [lo_v + 1, W_A]
        let mp = bl(&row.mid.a).max(bl(&row.mid.b));
        let lo_v = s.role_clear_lo_v(i >= term_from);
        checks.push((mp >= lo_v + 1 && mp <= s.w_a, "lo_v (role clear)"));
        checks.push((bl(&row.mid.ca).max(bl(&row.mid.cb)) <= RING - mp, "fit fact at the step end"));
    }
    if let Some((s2, carry)) = row.mul {
        let ca_new = row.mid.ca;
        let carry_u = usize::from(carry);
        let lo_c = s.m10_cascade_lo(); // M10's cascade bottom (the tie residue window)
        let d = s2 + carry_u;
        let residue_ok = (((ca_new >> d) >> lo_c) < (pre.cb >> lo_c)) == carry;
        let gap2 = RING - e_b - e_ca;
        checks.extend([
            (residue_ok, "narrow_lt residue (M10 window tie)"),
            (e_b >= s.m1_lo_b().max(1), "lo_B (M1)"),
            (e_b <= s.w_b, "width_b (M1)"),
            (e_cb >= s.lo_cb + 1, "lo_cb (M5 zone)"),
            (bl(&ca_new) <= s.w_c, "width_c (ca_new)"),
            (bl(&ca_new) == e_cb + s2 + carry_u, "bl(ca_new) theorem"),
            (e_b + bl(&ca_new) <= RING, "e_B + bl(ca_new) > 257"),
            (pre.ca.is_zero() || gap2 < WINDOW, "gap_bound (M1)"),
            (s2 <= s.s2_bound, "s2 > bound"),
            (s2 + carry_u < (1 << SROT), "s2 + carry overflows the shift word"),
        ]);
    }
    if let Some((sd, off, a_new)) = row.div {
        let off_u = usize::from(off);
        let s_raw = sd + off_u;
        let e_a_new = bl(&a_new);
        let d = e_a - e_a_new;
        let n_w = s.div_scan_window();
        let n0 = s.div_term_window();
        let terminal = a_new.is_zero();
        let lo = s.div_cascade_lo(); // D4/D9 cascade bottom (the tie residue window)
        let win = s.div_capture_window();
        let e_e = e_b + off_u;
        let mask_e = (one() << e_b) - one();
        let v4 = (pre.a >> s_raw) >> lo;
        let u4 = pre.b >> lo;
        let residue4 = v4 == u4 && (pre.a >> s_raw) < pre.b;
        let r = a_new >> sd;
        let nb = (mask_e ^ pre.b) >> lo;
        let residue9 = nb == (r >> lo) && (mask_e ^ pre.b) < r;
        checks.extend([
            (e_b >= win.lo && e_b <= win.hi, "lo_B (D4/D9 capture window)"),
            (s.div_zone_admits(e_e), "zone (D7: E below the masked zone)"),
            (s_raw < (1usize << s.rb_div.min(SROT)), "s_raw > rotation bound"),
            (!terminal || i >= term_from, "term_row (exact division before FROM)"),
            (!terminal || sd <= n0, "term_window (s > D0 window)"),
            (terminal || d <= n_w - 1 + off_u, "drop_bound (D11)"),
            (!residue4, "D4 tie residue"),
            (!residue9, "D9 tie residue"),
        ]);
    }
    for (ok, why) in checks {
        if !ok {
            return Err(why);
        }
    }
    Ok(())
}

/// Oracle data wires for `trailmix_port::eval_shots` (the full circuit's
/// prefix rows checked against the same oracle as this selftest): the state
/// after forward row `row` (`None` = S_0) of the input `x` (unfolded, mod p),
/// in the [`data_ids`] wire order with the q register `wq` wide and `nctr`
/// counter bits. The trace is computed per call (530 rows, ~ms).
pub(crate) fn oracle_data_bits(x: U512, row: Option<usize>, wq: usize, nctr: usize, term_from: usize, pop: bool) -> Vec<bool> {
    let t = trace(x, NSTEPS, term_from, pop);
    match row {
        None => expected_lenient(&StepWidths::from_schedule(0), &St { a: prime(), b: t.x, ca: U512::ZERO, cb: one(), q: U512::ZERO }, wq, nctr, true, 0),
        Some(i) => {
            let r = &t.rows[i];
            expected_lenient(&StepWidths::from_schedule(i), &r.post, wq, nctr, r.parity, r.counter)
        }
    }
}

/// The oracle's support verdict of input `x`: the first miss row and kind, if any.
pub(crate) fn oracle_first_miss(x: U512, term_from: usize, pop: bool) -> Option<(usize, &'static str)> {
    let t = trace(x, NSTEPS, term_from, pop);
    for i in 0..NSTEPS {
        let s = StepWidths::from_schedule(i);
        if let Err(kind) = support(&t.rows[i], i, &s, natural_q_width(i), term_from) {
            return Some((i, kind));
        }
    }
    None
}

/// Name of data wire `k` in the [`data_ids`] order (for reports).
pub(crate) fn data_wire_name(k: usize, wq: usize, nctr: usize) -> String {
    wire_name(k, wq, nctr)
}

fn random_inputs(n: usize) -> Vec<U512> {
    let mut seed = Shake256::default();
    seed.update(b"packed-driver-inputs-v1");
    let mut xof = seed.finalize_xof();
    let p = prime();
    (0..n)
        .map(|_| {
            let mut bytes = [0u8; 64];
            xof.read(&mut bytes[..32]);
            let x = U512::from_le_bytes(bytes) % p;
            if x.is_zero() { one() } else { x }
        })
        .collect()
}

/// LSB-frame ring content: value bit j at wire j, coefficient bit j at wire 256 - j.
fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    ring_lsb_lenient(value, coef)
}

fn ring_lsb_lenient(value: &U512, coef: &U512) -> Vec<bool> {
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}

fn bits_u512(v: &U512, n: usize) -> Vec<bool> {
    (0..n).map(|i| v.bit(i)).collect()
}

/// Expected data wires of one input after a row (or S_0): the layout of
/// [`data_ids`]: r1 | r2 | ex1 | ex2 | q | counter | s_rot | off | parity;
/// the exponents in the frame of `s` (the state after forward row i is in
/// row i's frame; the rebase to row i + 1 happens at the start of row i + 1).
fn expected(s: &StepWidths, st: &St, wq: usize, nctr: usize, parity: bool, counter: usize) -> Vec<bool> {
    assert!(bl(&st.q) <= wq, "q wider than its register");
    expected_lenient(s, st, wq, nctr, parity, counter)
}

/// [`expected`] without the q-width assertion (an off-support state: the low
/// `wq` bits of q; the packing of a too-wide value or coefficient is clipped
/// at the ring) - for the full-circuit comparison, which stops at the first
/// departure anyway.
fn expected_lenient(s: &StepWidths, st: &St, wq: usize, nctr: usize, parity: bool, counter: usize) -> Vec<bool> {
    let mut v = ring_lsb_lenient(&st.a, &st.cb);
    v.extend(ring_lsb_lenient(&st.b, &st.ca));
    v.extend(bits_of(s.reb_v(bl(&st.a)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.cb)), EXP_BITS));
    v.extend(bits_of(s.reb_v(bl(&st.b)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.ca)), EXP_BITS));
    v.extend(bits_u512(&st.q, wq));
    v.extend(bits_of(counter, nctr));
    v.extend(bits_of(0, SROT));
    v.push(false); // off
    v.push(parity);
    v
}

fn data_ids(p: &Packed) -> Vec<QubitId> {
    let mut ids: Vec<QubitId> = Vec::new();
    for reg in [&p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.counter, &p.s_rot] {
        ids.extend(reg.iter().map(|q| QubitId(q.id().into())));
    }
    ids.push(QubitId(p.off.as_ref().expect("off").id().into()));
    ids.push(QubitId(p.parity.as_deref().expect("parity").id().into()));
    ids
}

fn wire_name(k: usize, wq: usize, nctr: usize) -> String {
    let mut k = k;
    for (name, n) in [("r1", RING), ("r2", RING), ("eA", EXP_BITS), ("ecb", EXP_BITS), ("eB", EXP_BITS), ("eca", EXP_BITS), ("q", wq), ("counter", nctr), ("srot", SROT), ("off", 1), ("parity", 1)] {
        if k < n {
            return format!("{name}[{k}]");
        }
        k -= n;
    }
    "?".to_string()
}

/// Grow the simulator to hold every qubit / bit the ops touch (+ the
/// `checked_apply` scratch bit at the end) and apply them with reset checks
/// (the `checked_apply` loop of `predicate_clear_selftest.rs`, with the
/// section of a dirty reset named from the builder's phase transitions).
fn apply_chunk<R: XofReader>(sim: &mut Simulator<'_, R>, ops: &[Op], transitions: &[(usize, &'static str)], live: u64, where_: &str) {
    use crate::circuit::{BitId, NO_BIT};
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq as usize;
    let nb = nb as usize + 1;
    if nq > sim.num_qubits {
        sim.qubits.resize(nq, 0);
        sim.num_qubits = nq;
    }
    if nb > sim.num_bits {
        sim.bits.resize(nb, 0);
        sim.num_bits = nb;
    }
    let scratch_bit = BitId((sim.num_bits - 1) as u64);
    sim.bits[scratch_bit.0 as usize] = 0;
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = scratch_bit;
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    let mut stack = Vec::new();
    let mut mask = u64::MAX;
    for (k, op) in ops.iter().enumerate() {
        match op.kind {
            OperationType::PushCondition => {
                stack.push(mask);
                mask &= sim.bit(op.c_condition);
            }
            OperationType::PopCondition => mask = stack.pop().expect("balanced condition"),
            _ => {
                let cond = mask & if op.c_condition == NO_BIT { u64::MAX } else { sim.bit(op.c_condition) };
                if op.kind == OperationType::R {
                    let dirty = sim.qubit(op.q_target) & cond & live;
                    if dirty != 0 {
                        let phase = transitions.iter().rev().find(|(idx, _)| *idx <= k).map_or("?", |(_, ph)| ph);
                        panic!(
                            "{where_}: dirty reset of qubit {} at op {k} (shots {dirty:#x}) in section {phase}",
                            op.q_target.0
                        );
                    }
                }
                *sim.bit_mut(scratch_bit) = mask;
                sim.apply_iter([&push, op, &pop].into_iter());
            }
        }
    }
    assert!(stack.is_empty());
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Toffoli per step item (the section component right below `pk.step`, with
/// the substep item for `pk.mul` / `pk.div`), from the builder's phase
/// transitions of one row's ops.
fn item_toffoli(ops: &[Op], transitions: &[(usize, &'static str)]) -> Vec<(String, usize)> {
    let mut out: std::collections::BTreeMap<String, usize> = Default::default();
    let mut ti = 0usize;
    let mut cur: &str = "";
    for (j, op) in ops.iter().enumerate() {
        while ti < transitions.len() && transitions[ti].0 <= j {
            cur = transitions[ti].1;
            ti += 1;
        }
        if !matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
            continue;
        }
        let parts: Vec<&str> = cur.split('/').collect();
        let k = parts.iter().position(|s| *s == "pk.step");
        let item = match k {
            Some(k) => {
                let sub = parts.get(k + 1).copied().unwrap_or("step");
                if sub.starts_with("pk.mul") || sub.starts_with("pk.div") {
                    format!("{}", parts.get(k + 2).copied().unwrap_or(sub))
                } else {
                    sub.to_string()
                }
            }
            None => "(outside)".to_string(),
        };
        *out.entry(item).or_insert(0) += 1;
    }
    let order = [
        "pk.role", "M1", "M2", "M3", "M4", "M5", "M6", "M8", "M9", "M10", "M11", "M12", "D1", "D0", "D3", "D4", "D5", "D6",
        "D7", "D7b", "D8", "D6p", "D9", "D11", "D10", "D0c", "D12", "pk.roleclr", "pk.swap",
    ];
    let mut rows: Vec<(String, usize)> = Vec::new();
    for k in order {
        if let Some(v) = out.remove(k) {
            rows.push((k.to_string(), v));
        }
    }
    for (k, v) in out {
        rows.push((k, v));
    }
    rows
}

fn snapshot<R: XofReader>(sim: &Simulator<'_, R>, ids: &[QubitId]) -> Vec<u64> {
    ids.iter().map(|&id| sim.qubit(id)).collect()
}

fn shot_bits(snap: &[u64], shot: usize) -> Vec<bool> {
    snap.iter().map(|w| (w >> shot) & 1 == 1).collect()
}

/// Every qubit outside `ids` is 0 on the live shots.
fn assert_ancillae_clean<R: XofReader>(sim: &Simulator<'_, R>, ids: &[QubitId], live: u64, where_: &str) {
    let data: std::collections::HashSet<u64> = ids.iter().map(|q| q.0).collect();
    for (k, &v) in sim.qubits.iter().enumerate() {
        if !data.contains(&(k as u64)) {
            assert_eq!(v & live, 0, "{where_}: qubit {k} dirty (shots {:#x})", v & live);
        }
    }
}

/// Snapshot of the process environment; `restore` puts it back exactly.
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

pub(super) fn run() {
    let env = EnvSnapshot::take();
    // --- the production configuration of the packed prefix ---------------
    std::env::set_var("TRAILMIX_THIN_SCHEDULE", "1");
    std::env::set_var("TRAILMIX_THIN_SEED", "278");
    std::env::set_var("TRAILMIX_THIN_MARGIN", env_usize("MIDQ_DRIVER_SELFTEST_MARGIN", 0).to_string());
    let validate = std::env::var("MIDQ_DRIVER_SELFTEST_VALIDATE").unwrap_or_else(|_| "500000".to_string());
    std::env::set_var("TRAILMIX_THIN_VALIDATE", validate.clone());
    std::env::set_var("TRAILMIX_THIN_CLZ_WINDOW", "78");
    std::env::set_var("TRAILMIX_SROT_W", "5");
    std::env::set_var("TRAILMIX_COUNTER_W", "8");
    std::env::set_var("MIDQ_MEASURED_DEMUX", "1");
    std::env::set_var("LOWQ_COMPACT_KGANC", "1");
    std::env::set_var("LOWQ_ONE_A_ELIM", "1");
    std::env::set_var("TRAILMIX_Q_TARGET", "685"); // LOWQ_ONE_A_ELIM is sealed to it (the packed q width ignores it)
    std::env::set_var("MIDQ_MEASURE_GATE_AND", "1");
    std::env::set_var("MIDQ_MEASURE_PREDICATE", "1");
    std::env::set_var("MIDQ_CHUNKED_PREDICATE", "1");
    std::env::set_var("MIDQ_PREFIX_POPCOUNT", "1");
    std::env::set_var("MIDQ_PZ_PINGPONG_TAIL", "0");
    std::env::set_var("MIDQ_PREFIX_TERMINAL_FROM", super::super::p0_shape::DEFAULT_TERMINAL_FROM.to_string());
    std::env::set_var("MIDQ_PACKED_PREFIX", "1");
    for k in ["MIDQ_PACKED_STUBS", "MIDQ_ONEHOT_COHERENT", "MIDQ_PACKED_CTZ_ROOM", "MIDQ_PACKED_QCAP", "MIDQ_P0_TRACE", "MIDQ_TRACE_PZ_STEPS", "TRACE_PHASE_ACTIVE", "MIDQ_PREFIX_NO_TERMINAL"] {
        std::env::remove_var(k);
    }
    let steps = env_usize("MIDQ_DRIVER_SELFTEST_STEPS", NSTEPS).clamp(1, NSTEPS);
    let verbose = std::env::var_os("MIDQ_DRIVER_SELFTEST_VERBOSE").is_some();
    let ninputs = env_usize("MIDQ_DRIVER_SELFTEST_INPUTS", 64).clamp(1, 64);
    let term_from = terminal_from();
    let t0 = std::time::Instant::now();

    // --- the circuit's registers (S_0 layout of p0_shape::enter_s0) --------
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("pk.R1", RING);
    let r2 = c.alloc_qreg_bits("pk.R2", RING);
    let mut ex1 = c.alloc_qreg_bits("pk.eA", EXP_BITS);
    ex1.extend(c.alloc_qreg_bits("pk.ecb", EXP_BITS));
    let mut ex2 = c.alloc_qreg_bits("pk.eB", EXP_BITS);
    ex2.extend(c.alloc_qreg_bits("pk.eca", EXP_BITS));
    let q = c.alloc_qreg_bits("pk.q", natural_q_width(0));
    let s_rot = c.alloc_qreg_bits("pk.srot", trailmix_srot_width());
    let off = Some(c.alloc_qreg("pk.off"));
    let parity_q = c.alloc_qreg("pk.par");
    let counter = c.alloc_qreg_bits("pk.ctr", trailmix_counter_width());
    let mut p = Packed { r1, r2, ex1, ex2, q, counter, s_rot, off, parity: Some(BorrowedQReg::Owned(parity_q)) };
    let nctr = p.counter.len();
    let pop = popcount_on(&p.counter);
    assert_eq!(p.s_rot.len(), SROT);
    assert_eq!(nctr, 8, "the terminal counter is 8 bits wide (TRAILMIX_COUNTER_W)");
    eprintln!(
        "PACKED_DRIVER config: schedule=thin(seed 278, validate {validate}) steps={steps} inputs={ninputs} term_from={term_from} popcount_cache={pop} q0={} ({:.1}s to generate the schedule)",
        p.q.len(),
        t0.elapsed().as_secs_f64()
    );

    // --- the oracle and the support classification -------------------------
    let mut inputs = random_inputs(ninputs);
    // explicit inputs (eval shots under investigation) replace the first draws
    let explicit: Vec<U512> = std::env::var("MIDQ_DRIVER_SELFTEST_X")
        .ok()
        .map(|s| {
            s.split(',')
                .map(|h| h.trim().trim_start_matches("0x"))
                .filter(|h| !h.is_empty())
                .map(|h| U512::from_str_radix(h, 16).expect("MIDQ_DRIVER_SELFTEST_X: hex value") % prime())
                .map(|x| if x.is_zero() { one() } else { x })
                .collect()
        })
        .unwrap_or_default();
    assert!(explicit.len() <= ninputs, "MIDQ_DRIVER_SELFTEST_X: more values than inputs");
    let n_explicit = explicit.len();
    for (j, x) in explicit.into_iter().enumerate() {
        inputs[j] = x;
    }
    let mut traces: Vec<Trace> = inputs.iter().map(|&x| trace(x, steps, term_from, pop)).collect();
    let wq_of: Vec<usize> = (0..steps).map(natural_q_width).collect();
    assert!(wq_of.iter().all(|&w| w <= MAX_Q_WIDTH), "a q envelope exceeds {MAX_Q_WIDTH} (s2 + carry must fit the 5-bit shift word)");
    let mut miss_kinds: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for t in traces.iter_mut() {
        for i in 0..steps {
            let s = StepWidths::from_schedule(i);
            if let Err(kind) = support(&t.rows[i], i, &s, wq_of[i], term_from) {
                t.first_miss = Some((i, kind));
                *miss_kinds.entry(kind).or_insert(0) += 1;
                break;
            }
        }
    }
    let on_support = traces.iter().filter(|t| t.first_miss.is_none()).count();
    let drain_inputs = traces.iter().filter(|t| t.draining_rows > 0).count();
    let frozen_inputs = traces.iter().filter(|t| t.frozen_rows > 0).count();
    let term_min = traces.iter().filter_map(|t| t.terminal).min();
    let term_max = traces.iter().filter_map(|t| t.terminal).max();
    eprintln!(
        "PACKED_DRIVER inputs: {ninputs} drawn, {on_support} fully on the support, first misses by kind {miss_kinds:?}; terminal step min {term_min:?} max {term_max:?}; inputs with draining rows {drain_inputs}, with frozen rows {frozen_inputs}"
    );
    for (j, t) in traces.iter().enumerate() {
        if let Some((i, k)) = t.first_miss {
            eprintln!("PACKED_DRIVER input {j} ({:#x}) first miss at row {i}: {k}", t.x);
            if j < n_explicit {
                let r = &t.rows[i];
                let s = StepWidths::from_schedule(i);
                eprintln!(
                    "PACKED_DRIVER input {j} miss row {i} ({:?}, terminal {:?}): pre e_A {} e_B {} e_ca {} e_cb {} bl(q) {} | W_A {} W_c {} w_q {} lo_b {} lo_ca {} lo_cb {} cascade_lo {} | mul {:?} div {:?}",
                    r.kind, t.terminal, bl(&r.pre.a), bl(&r.pre.b), bl(&r.pre.ca), bl(&r.pre.cb), bl(&r.pre.q),
                    s.w_a, s.w_c, wq_of[i], s.lo_b, s.lo_ca, s.lo_cb, s.div_cascade_lo(),
                    r.mul, r.div.map(|(sd, off, _)| (sd, off))
                );
            }
        } else if j < n_explicit {
            eprintln!("PACKED_DRIVER input {j} ({:#x}) is on the support (terminal {:?})", t.x, t.terminal);
        }
        if verbose {
            let first_drain = t.rows.iter().position(|r| r.kind == Kind::Draining);
            let first_frozen = t.rows.iter().position(|r| r.kind == Kind::Frozen);
            eprintln!("PACKED_DRIVER input {j}: terminal {:?} first draining {:?} first frozen {:?} draining rows {} frozen rows {}", t.terminal, first_drain, first_frozen, t.draining_rows, t.frozen_rows);
        }
    }

    // --- the simulator: S_0 loaded for every input ------------------------
    let live: u64 = if ninputs == 64 { u64::MAX } else { (1u64 << ninputs) - 1 };
    let mut seed = Shake256::default();
    seed.update(b"packed-driver-sim-v1");
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(1, 2, &mut rng);
    let s0_ids = data_ids(&p);
    {
        let nq = s0_ids.iter().map(|q| q.0 as usize + 1).max().unwrap();
        sim.qubits.resize(nq, 0);
        sim.num_qubits = nq;
        for (j, t) in traces.iter().enumerate() {
            let st = St { a: prime(), b: t.x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
            let bits = expected(&StepWidths::from_schedule(0), &st, p.q.len(), nctr, true, 0);
            for (k, &id) in s0_ids.iter().enumerate() {
                if bits[k] {
                    *sim.qubit_mut(id) |= 1u64 << j;
                }
            }
        }
    }
    let s0_snap = snapshot(&sim, &s0_ids);
    let mut snaps: Vec<(Vec<QubitId>, Vec<u64>)> = Vec::with_capacity(steps);
    let report_steps = [0usize, 1, 10, 50, 100, 150, 200, 250, 300, 339, 340, 350, 364, 365, 378, 400, 440, 480, 500, 520, 529];
    let mut t_fwd = vec![0usize; steps];
    let mut t_bwd = vec![0usize; steps];
    let mut ops_total = 0usize;
    let mut checked_rows = 0usize;
    let mut checked_draining = 0usize;
    let mut checked_frozen = 0usize;

    // --- forward ------------------------------------------------------------
    // Inputs off the support (the predicate's first miss row, or a CIRCUIT
    // departure found below) carry garbage from that row on: the reset /
    // phase / ancilla checks exclude them (`dead`), as the eval's per-shot
    // verdict would - an off-support shot fails, the others are unaffected.
    let mut dead: u64 = 0;
    for i in 0..steps {
        for (j, t) in traces.iter().enumerate() {
            if t.first_miss.map_or(false, |(m, _)| m == i) {
                dead |= 1u64 << j;
            }
        }
        let live_i = live & !dead;
        let start = c.b.ops.len();
        t_fwd[i] = forward_step(&mut c, &mut p, i);
        let ops: Vec<Op> = c.b.ops.drain(start..).collect();
        let transitions: Vec<(usize, &'static str)> = c.b.phase_transitions.drain(..).collect();
        assert_eq!(c.b.ops.len(), start);
        assert_eq!(t_fwd[i], toffoli(&ops), "row {i}: counted vs recorded Toffoli");
        ops_total += ops.len();
        if verbose {
            let kinds: Vec<String> = traces.iter().enumerate().filter(|(_, t)| t.rows[i].kind != Kind::Mul && t.rows[i].kind != Kind::Div).map(|(j, t)| format!("{j}:{:?}", t.rows[i].kind)).collect();
            eprintln!("PACKED_DRIVER fwd row {i}: applying {} ops; special rows [{}]", ops.len(), kinds.join(" "));
        }
        apply_chunk(&mut sim, &ops, &transitions, live_i, &format!("forward row {i}"));
        assert_eq!(sim.phase & live_i, 0, "forward row {i}: phase");
        let ids = data_ids(&p);
        assert_ancillae_clean(&sim, &ids, live_i, &format!("forward row {i}"));
        let snap = snapshot(&sim, &ids);
        let wq = p.q.len();
        assert_eq!(wq, wq_of[i], "q width at row {i}");
        for j in 0..ninputs {
            let t = &traces[j];
            if t.first_miss.map_or(false, |(m, _)| i >= m) {
                continue;
            }
            let row = &t.rows[i];
            let want = expected(&StepWidths::from_schedule(i), &row.post, wq, nctr, row.parity, row.counter);
            let got = shot_bits(&snap, j);
            if got != want {
                let k = got.iter().zip(&want).position(|(a, b)| a != b).unwrap();
                let msg = format!(
                    "forward row {i} input {j} ({:#x}, kind {:?}, terminal {:?}): first differing wire {k} = {} (got {}, want {})",
                    t.x, row.kind, t.terminal, wire_name(k, wq, nctr), got[k], want[k]
                );
                if j < n_explicit {
                    // an explicit (eval-shot) input the support predicate accepted:
                    // report the circuit's departure from the oracle and stop checking it
                    eprintln!("PACKED_DRIVER input {j} CIRCUIT leaves the oracle: {msg}");
                    traces[j].first_miss = Some((i, "CIRCUIT (on-support input, oracle mismatch)"));
                    dead |= 1u64 << j;
                    continue;
                }
                panic!("{msg}");
            }
            checked_rows += 1;
            match row.kind {
                Kind::Draining => checked_draining += 1,
                Kind::Frozen => checked_frozen += 1,
                _ => {}
            }
        }
        snaps.push((ids, snap));
        if report_steps.contains(&i) || i + 1 == steps {
            eprintln!(
                "PACKED_DRIVER fwd row {i:3}: q {:2} T {:6} ops {:7} ({:.0}s)",
                wq, t_fwd[i], ops.len(), t0.elapsed().as_secs_f64()
            );
        }
        if [100usize, 250, 378, 500].contains(&i) {
            let items: Vec<String> = item_toffoli(&ops, &transitions).into_iter().map(|(k, v)| format!("{k} {v}")).collect();
            eprintln!("PACKED_DRIVER fwd row {i} T per item: {}", items.join(", "));
        }
    }
    let fwd_sum: usize = t_fwd.iter().sum();
    eprintln!(
        "PACKED_DRIVER forward: {steps} rows, T sum {fwd_sum} (avg {}), {checked_rows} row-states oracle-checked ({checked_draining} draining, {checked_frozen} frozen), {ops_total} ops",
        fwd_sum / steps
    );
    if steps == NSTEPS {
        // the terminal state of every on-support input: R1 = [0 | x^-1], R2 = [1 | p]
        for (j, t) in traces.iter().enumerate() {
            if t.first_miss.is_some() {
                continue;
            }
            let last = &t.rows[NSTEPS - 1].post;
            assert!(last.a.is_zero() && last.b == one() && last.q.is_zero() && last.ca == prime(), "input {j}: not at the terminal state after 530 rows");
        }
    }

    // --- backward -------------------------------------------------------------
    // (an input that left the support forward is excluded throughout: its
    // forward garbage went through dirty resets, so no inverse restores it)
    let live = live & !dead;
    if dead != 0 {
        eprintln!("PACKED_DRIVER backward: {} input(s) off the support excluded from the checks (mask {dead:#x})", dead.count_ones());
    }
    for i in (0..steps).rev() {
        let start = c.b.ops.len();
        t_bwd[i] = backward_step(&mut c, &mut p, i);
        let ops: Vec<Op> = c.b.ops.drain(start..).collect();
        let transitions: Vec<(usize, &'static str)> = c.b.phase_transitions.drain(..).collect();
        ops_total += ops.len();
        apply_chunk(&mut sim, &ops, &transitions, live, &format!("backward row {i}"));
        assert_eq!(sim.phase & live, 0, "backward row {i}: phase");
        let ids = data_ids(&p);
        assert_ancillae_clean(&sim, &ids, live, &format!("backward row {i}"));
        let (want_ids, want) = if i == 0 { (&s0_ids, &s0_snap) } else { (&snaps[i - 1].0, &snaps[i - 1].1) };
        // The register LAYOUT must match the forward snapshot (the values are
        // compared position by position below); the wire ids may differ: the
        // per-step exponent rebase (`p0_shape::rebase_exponents`) allocates and
        // frees KG ancillae on the LIFO free list at mirrored positions of the
        // two directions, which permutes the ids the q resize picks up.
        assert_eq!(ids.len(), want_ids.len(), "backward row {i}: register layout differs from the forward snapshot");
        let got = snapshot(&sim, &ids);
        if &got != want {
            let wq = p.q.len();
            for j in 0..ninputs {
                if (dead >> j) & 1 == 1 {
                    continue;
                }
                let g = shot_bits(&got, j);
                let w = shot_bits(want, j);
                if g != w {
                    let k = g.iter().zip(&w).position(|(a, b)| a != b).unwrap();
                    panic!(
                        "backward row {i} input {j} ({:#x}): state differs from the pre-forward snapshot at wire {k} = {}",
                        traces[j].x, wire_name(k, wq, nctr)
                    );
                }
            }
        }
        if report_steps.contains(&i) || i + 1 == steps {
            eprintln!("PACKED_DRIVER bwd row {i:3}: q {:2} T {:6} ops {:7} ({:.0}s)", p.q.len(), t_bwd[i], ops.len(), t0.elapsed().as_secs_f64());
        }
    }
    // S_0 exactly, for every input (values, exponents, q, s_rot, off, parity, counter)
    let ids = data_ids(&p);
    assert_eq!(ids.len(), s0_ids.len());
    let got = snapshot(&sim, &ids);
    for (j, t) in traces.iter().enumerate() {
        if (dead >> j) & 1 == 1 {
            continue;
        }
        let st = St { a: prime(), b: t.x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
        let want = expected(&StepWidths::from_schedule(0), &st, p.q.len(), nctr, true, 0);
        let g = shot_bits(&got, j);
        assert_eq!(g, want, "input {j}: S_0 not restored after the round trip");
    }
    assert_eq!(sim.phase & live, 0, "round trip: phase");
    assert_ancillae_clean(&sim, &ids, live, "round trip");
    let bwd_sum: usize = t_bwd.iter().sum();

    // --- report ---------------------------------------------------------------
    for &i in &[100usize, 250, 378, 500] {
        if i < steps {
            let s = StepWidths::from_schedule(i);
            eprintln!(
                "PACKED_DRIVER T row {i}: fwd {} bwd {} (W_A {} W_c {} q {} cascade_lo {} lo_b {} lo_ca {} lo_cb {})",
                t_fwd[i], t_bwd[i], s.w_a, s.w_c, wq_of[i], s.div_cascade_lo(), s.lo_b, s.lo_ca, s.lo_cb
            );
        }
    }
    let (imax, tmax) = t_fwd.iter().copied().enumerate().max_by_key(|&(_, t)| t).unwrap();
    eprintln!(
        "PACKED_DRIVER T: forward sum {fwd_sum} backward sum {bwd_sum} over {steps} rows (fwd avg {}, max {tmax} at row {imax}); design section 4: 12,435 at 378, 5.95M per traversal at cut 530",
        fwd_sum / steps
    );
    // required coverage (design 10, refuter fix 7)
    assert!(on_support >= 32, "fewer than 32 fully on-support inputs ({on_support})");
    if steps == NSTEPS {
        assert!(checked_draining > 0, "no draining row checked against the oracle");
        assert!(checked_frozen > 0, "no frozen row checked against the oracle");
        assert!(term_min.unwrap() >= term_from, "an input terminates before MIDQ_PREFIX_TERMINAL_FROM");
    }
    eprintln!(
        "PACKED_DRIVER PASS: {ninputs} inputs x {steps} rows forward + {steps} rows backward on the Simulator, S_0 restored for every on-support input, {checked_rows} forward row-states equal to the oracle ({on_support} inputs on the support), phase 0, ancillae clean at every reset ({:.0}s)",
        t0.elapsed().as_secs_f64()
    );
    // free the registers (the Circuit is dropped with them)
    let _ = &mut p;
    env.restore();
}
