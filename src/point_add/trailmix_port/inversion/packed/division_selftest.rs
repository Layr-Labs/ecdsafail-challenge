//! Selftest for the packed division (`division.rs`) on REAL packed-prefix
//! states, in the `retained_division.rs:130-231` style: the exact `pz_prefix`
//! recurrence of `tools/packed_prefix_model.py` (single-q Kaliski step, 530
//! rows) is run in U512 on 64 Shake256-seeded inputs; at EVERY row `0..530`
//! the state at the division moment (after the row's multiply) is loaded into
//! a `Circuit` in the packed layout (`R1 = [A | gap | cb]`, `R2 = [B | gap |
//! ca]`, the four exponents, `q` at the schedule width, `s_rot = off = term =
//! 0`), `division_forward` is applied with `gate_div = 1` on division rows
//! and `0` on multiply-only / draining / frozen rows (the terminal predicate
//! wire is passed on rows >= `MIDQ_PREFIX_TERMINAL_FROM`), and the result is
//! read back: `A' = A - (B << s)`, `q' = q ^ (1 << s)`, `e_A' = bl(A')` (0 on
//! the terminal row), `s_rot`, `off`, `term` cleared, `R2`, `e_B`, `e_ca`,
//! `e_cb`, cb's bits and q's other bits untouched, gate-0 rows byte-identical;
//! phase 0 and every freed ancilla 0 (`checked_apply` asserts at each reset).
//! Then `division_backward` on the outputs must restore the inputs exactly
//! (every row, every step). Rows off the support (width, `lo_b`, `drop_bound`,
//! `term_row`, the D4/D9 tie residue) are counted per kind and excluded from
//! the value claim only. Also: the division rows with `gate = 0` (every 25th
//! step), random garbage round trips (a few steps), and the required classes
//! (tight packing = R1 gap 0, `e_A = W_A` with off = 0, B = 1 rows with `term`
//! (exact and inexact), draining rows with `term` live) are counted and
//! asserted non-empty. Prints the measured Toffoli per step (both directions)
//! and per item at selected steps.
//!
//! Schedule: the static tables (`TRAILMIX_THIN_SCHEDULE` unset) through
//! `sched::StepWidths::from_schedule` (the driver's geometry: every `lo` from
//! `thin_lo`, the D4/D9 cascade bottom `max(0, lo_b - 32)`, the D7 zone from
//! `min(257 - W_c, lo_b + 1)`); `MIDQ_DIVISION_SELFTEST_THIN=1` runs the thin
//! schedule instead (65k training draws, slower).

use super::super::super::env_usize;
use super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::BTreeMap;

/// Adversarial review cases (2026-09-14): real inputs from a 160k classical
/// search and synthetic rows at the class boundaries; runs inside `run()`.
#[path = "division_review_cases.rs"]
mod review;

const NSTEPS: usize = 530;
const NINPUTS: usize = 64;
const SROT: usize = 5;

fn p() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}

fn bl(x: &U512) -> usize {
    x.bit_len()
}

fn one() -> U512 {
    U512::from(1u64)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// The division fires (`gate_div = 1`).
    Div,
    /// A multiply fired, no division (A < B).
    MulOnly,
    /// Neither substep (A < B, q = 0, A != 0): not expected on the walk.
    Idle,
    /// A = 0, B = 1, q != 0: a plain multiply row.
    Draining,
    /// A = 0, B = 1, q = 0: registers held.
    Frozen,
}

/// The state at the division moment of one row (after the row's multiply).
#[derive(Clone)]
struct Row {
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: U512,
    kind: Kind,
    s: usize,
    off: bool,
    a_new: U512,
}

impl Row {
    fn terminal(&self) -> bool {
        self.kind == Kind::Div && self.a_new.is_zero()
    }
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) recording the state
/// at every row's division moment and the division's result.
fn trace(x_orig: U512) -> Vec<Row> {
    let p = p();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, one(), U512::ZERO);
    let mut rows = Vec::with_capacity(NSTEPS);
    for step in 0..NSTEPS {
        assert!(a * cb + b * (ca + q * cb) == p, "row invariant at step {step}");
        if a.is_zero() && b == one() && q.is_zero() {
            rows.push(Row { a, b, ca, cb, q, kind: Kind::Frozen, s: 0, off: false, a_new: a });
            continue;
        }
        let mut mul = false;
        if a < b && !q.is_zero() {
            let s2 = q.trailing_zeros();
            q ^= one() << s2;
            ca += cb << s2;
            mul = true;
        }
        let mut row = Row {
            a,
            b,
            ca,
            cb,
            q,
            kind: if a.is_zero() { Kind::Draining } else if mul { Kind::MulOnly } else { Kind::Idle },
            s: 0,
            off: false,
            a_new: a,
        };
        if ca < cb {
            let s_raw = bl(&a) as i64 - bl(&b) as i64;
            if s_raw >= 0 {
                let off = a < (b << (s_raw as usize));
                let s = s_raw - i64::from(off);
                if s >= 0 {
                    let s = s as usize;
                    let bsh = b << s;
                    assert!(a >= bsh, "model: A < B << s at step {step}");
                    let a_new = a - bsh;
                    row.kind = Kind::Div;
                    row.s = s;
                    row.off = off;
                    row.a_new = a_new;
                    a = a_new;
                    q ^= one() << s;
                }
            }
        }
        // the design's exact role rule: the division fires iff A >= B
        assert_eq!(row.kind == Kind::Div, row.a >= row.b, "role rule at step {step}");
        rows.push(row);
        if q.is_zero() && !a.is_zero() {
            std::mem::swap(&mut a, &mut b);
            std::mem::swap(&mut ca, &mut cb);
        }
    }
    assert!(a.is_zero() && q.is_zero(), "input did not terminate by {NSTEPS}");
    rows
}

/// LSB-frame ring content: value bit j at wire j, coefficient bit j at wire
/// 256 - j. Asserts the packing invariant.
fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}

fn bits_u512(v: &U512, n: usize) -> Vec<bool> {
    (0..n).map(|i| v.bit(i)).collect()
}

fn random_inputs() -> Vec<U512> {
    let mut seed = Shake256::default();
    seed.update(b"packed-division-inputs-v1");
    let mut xof = seed.finalize_xof();
    let p = p();
    (0..NINPUTS)
        .map(|_| {
            let mut bytes = [0u8; 64];
            xof.read(&mut bytes[..32]);
            let x = U512::from_le_bytes(bytes) % p;
            if x.is_zero() { one() } else { x }
        })
        .collect()
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Peak number of live scratch wires above the data registers.
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
    /// Toffoli per design item (the `pk.div/<item>` section component).
    items: BTreeMap<String, usize>,
    /// Peak live scratch (wires above the data registers) per design item.
    item_scratch: BTreeMap<String, usize>,
}

fn ids(regs: &[&[QReg]]) -> Vec<QubitId> {
    regs.iter().flat_map(|r| r.iter().map(|q| QubitId(q.id().into()))).collect()
}

/// Toffoli and peak live scratch per section component right below
/// `pk.div` / `pk.div.inv`, from the builder's phase transitions (a non-data
/// qubit is live from its first touch after its last reset until that reset).
fn item_profile(c: &Circuit, data: &[QubitId]) -> (BTreeMap<String, usize>, BTreeMap<String, usize>) {
    use crate::circuit::NO_QUBIT;
    let mut t_out = BTreeMap::new();
    let mut s_out = BTreeMap::new();
    let data: std::collections::HashSet<u64> = data.iter().map(|q| q.0).collect();
    let mut live: std::collections::HashSet<u64> = std::collections::HashSet::new();
    let tr = &c.b.phase_transitions;
    let ops = &c.b.ops;
    let mut ti = 0usize;
    let mut cur: &str = "";
    for (j, op) in ops.iter().enumerate() {
        while ti < tr.len() && tr[ti].0 <= j {
            cur = tr[ti].1;
            ti += 1;
        }
        let item = cur
            .split('/')
            .skip_while(|s| !s.starts_with("pk.div"))
            .nth(1)
            .unwrap_or("(outside)")
            .to_string();
        for q in [op.q_control2, op.q_control1, op.q_target] {
            if q != NO_QUBIT && !data.contains(&q.0) {
                live.insert(q.0);
            }
        }
        let e = s_out.entry(item.clone()).or_insert(0);
        *e = (*e).max(live.len());
        if op.kind == OperationType::R {
            live.remove(&op.q_target.0);
        }
        if matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
            *t_out.entry(item).or_insert(0) += 1;
        }
    }
    (t_out, s_out)
}

/// Data wires: [r1(257) | r2(257) | ex1(18) | ex2(18) | q(wq) | s_rot(5) | off | gate | term].
fn build(sched: &StepWidths, wq: usize, with_term: bool, inverse: bool) -> Harness {
    build_variant(sched, wq, with_term, inverse, false)
}

fn build_variant(sched: &StepWidths, wq: usize, with_term: bool, inverse: bool, supported: bool) -> Harness {
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("r1", RING);
    let r2 = c.alloc_qreg_bits("r2", RING);
    let ex1 = c.alloc_qreg_bits("ex1", 2 * EXP_BITS);
    let ex2 = c.alloc_qreg_bits("ex2", 2 * EXP_BITS);
    let q = c.alloc_qreg_bits("q", wq);
    let s_rot = c.alloc_qreg_bits("srot", SROT);
    let off = c.alloc_qreg("off");
    let gate = c.alloc_qreg("gate");
    let term = c.alloc_qreg("term");
    let ids = ids(&[&r1, &r2, &ex1, &ex2, &q, &s_rot, std::slice::from_ref(&off), std::slice::from_ref(&gate), std::slice::from_ref(&term)]);
    let start = c.b.ops.len();
    let t = with_term.then_some(&term);
    if supported {
        division_supported(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, t, sched.step, sched, inverse);
    } else if inverse {
        division_backward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, t, sched.step, sched);
    } else {
        division_forward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, t, sched.step, sched);
    }
    let t = toffoli(&c.b.ops[start..]);
    let scratch = peak_scratch(&c.b.ops[start..], &ids);
    let (items, item_scratch) = item_profile(&c, &ids);
    Harness { ops: c.b.ops.clone(), ids, t, scratch, items, item_scratch }
}

/// Run up to 64 shots: load the data wires, apply with reset checks, assert
/// phase 0 and every non-data qubit 0, return the data wires per shot.
fn simulate(h: &Harness, shots: &[Vec<bool>], label: &str) -> Vec<Vec<bool>> {
    assert!(!shots.is_empty() && shots.len() <= 64);
    let (nq, nb, _, _) = analyze_ops(h.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-division-sim-v1");
    seed.update(label.as_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for (shot, data) in shots.iter().enumerate() {
        assert_eq!(data.len(), h.ids.len(), "{label}: data width");
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
    supported_checked: usize,
    rows: usize,
    div_rows: usize,
    div_checked: usize,
    gate0_rows: usize,
    mul_only: usize,
    draining: usize,
    draining_term_live: usize,
    frozen: usize,
    idle: usize,
    tight: usize,
    ea_eq_wa_off0: usize,
    off1: usize,
    b_one_terminal: usize,
    b_one_inexact: usize,
    terminal_rows: usize,
    terminal_steps_min: usize,
    d_max: usize,
    s_max: usize,
    s_raw_max: usize,
    e_b_min_margin: usize,
    zone_cells_max: usize,
    gate0_variant: usize,
    garbage_rt: usize,
    inverse_checked: usize,
    // misses
    miss_width_a: usize,
    miss_width_q: usize,
    miss_lo_b: usize,
    miss_rot: usize,
    miss_drop: usize,
    miss_term_row: usize,
    miss_term_window: usize,
    miss_residue4: usize,
    miss_residue9: usize,
    miss_exp_range: usize,
}

struct Shot {
    data: Vec<bool>,
    expect: Vec<bool>,
    /// The value claim holds (gate-0 row or on-support division row).
    check: bool,
}

/// One shot from a row at `sched` (q width `wq`, the term wire live when
/// `with_term`); `gate` forces the division gate (a division row with
/// `gate = false` is the gate-0 variant).
fn shot(row: &Row, sched: &StepWidths, wq: usize, with_term: bool, gate: bool, cnt: &mut Counts) -> Shot {
    let e_a = bl(&row.a);
    let e_b = bl(&row.b);
    let e_ca = bl(&row.ca);
    let e_cb = bl(&row.cb);
    let mut data = ring_lsb(&row.a, &row.cb);
    data.extend(ring_lsb(&row.b, &row.ca));
    // the exponents in the row's rebased frame (sched.rs: e - base mod 2^7)
    data.extend(bits_of(sched.reb_v(e_a), EXP_BITS));
    data.extend(bits_of(sched.reb_c(e_cb), EXP_BITS));
    data.extend(bits_of(sched.reb_v(e_b), EXP_BITS));
    data.extend(bits_of(sched.reb_c(e_ca), EXP_BITS));
    // q wider than its envelope (bl(q) > wq, or bit s outside it) is the
    // `width_q` miss classified below: the loaded q is truncated, the row is
    // inverse-checked only (review 2026-09-14: the former assert here fired
    // under the thin schedule on the adversarial inputs before the
    // classification could count it).
    data.extend(bits_u512(&row.q, wq));
    data.extend(bits_of(0, SROT));
    data.push(false); // off
    data.push(gate);
    data.push(false); // term
    if !gate {
        return Shot { data: data.clone(), expect: data, check: true };
    }
    assert_eq!(row.kind, Kind::Div);
    // ---- support classification --------------------------------------
    let e_a_new = bl(&row.a_new);
    let off = usize::from(row.off);
    let s_raw = row.s + off;
    let d = e_a - e_a_new;
    let n_w = sched.div_scan_window();
    let n0 = sched.div_term_window();
    let win = sched.div_capture_window();
    let terminal = row.terminal();
    let mut on_support = true;
    if e_a > sched.w_a || e_b > sched.w_a {
        cnt.miss_width_a += 1;
        on_support = false;
    }
    // exp_range: an exponent outside the row's rebase window [base, base + 127]
    if !sched.v_in_range(e_a) || !sched.v_in_range(e_b) || !sched.v_in_range(e_a_new) || !sched.c_in_range(e_ca) || !sched.c_in_range(e_cb) {
        cnt.miss_exp_range += 1;
        on_support = false;
    }
    let q_new = row.q ^ (one() << row.s);
    if bl(&q_new) > wq || bl(&row.q) > wq {
        cnt.miss_width_q += 1;
        on_support = false;
    }
    // `lo_b`: e_B below the D4/D9 capture window (lo_b + 1 while lo_b > 32,
    // else 1), or the D7 toggle leaf E = e_B + off below the masked zone
    // (review 2026-09-14: `E < zone_start` leaves every window cell plain).
    if e_b < win.lo || !sched.div_zone_admits(e_b + off) {
        cnt.miss_lo_b += 1;
        on_support = false;
    }
    if s_raw >= (1usize << sched.rb_div.min(SROT)) {
        cnt.miss_rot += 1;
        on_support = false;
    }
    if terminal {
        if !with_term {
            cnt.miss_term_row += 1;
            on_support = false;
        } else if row.s > n0 {
            cnt.miss_term_window += 1;
            on_support = false;
        }
    } else if d > n_w - 1 + off {
        cnt.miss_drop += 1;
        on_support = false;
    }
    // D4 / D9 tie residue below the cascade bottom max(0, lo_b - 32) (the
    // compare windows tie: the captured flag is 0 whatever the low bits say)
    let lo = sched.div_cascade_lo();
    let mask_e = (one() << e_b) - one();
    let v4 = (row.a >> s_raw) >> lo;
    let u4 = row.b >> lo;
    if v4 == u4 && (row.a >> s_raw) < row.b {
        cnt.miss_residue4 += 1;
        on_support = false;
    }
    let r = row.a_new >> row.s;
    assert!(r < (one() << e_b), "R has a bit at e_B");
    let nb = (mask_e ^ row.b) >> lo; // ~B on e_B bits
    let rr = r >> lo;
    if nb == rr && (mask_e ^ row.b) < r {
        cnt.miss_residue9 += 1;
        on_support = false;
    }
    // classes
    cnt.div_rows += 1;
    if on_support {
        cnt.div_checked += 1;
        if RING - e_a - e_cb == 0 { cnt.tight += 1; }
        if e_a == sched.w_a && !row.off { cnt.ea_eq_wa_off0 += 1; }
        if row.off { cnt.off1 += 1; }
        if e_b == 1 {
            if terminal { cnt.b_one_terminal += 1; } else { cnt.b_one_inexact += 1; }
        }
        if terminal { cnt.terminal_rows += 1; cnt.terminal_steps_min = cnt.terminal_steps_min.min(sched.step); }
        if !terminal { cnt.d_max = cnt.d_max.max(d); }
        cnt.s_max = cnt.s_max.max(row.s);
        cnt.s_raw_max = cnt.s_raw_max.max(s_raw);
        cnt.e_b_min_margin = cnt.e_b_min_margin.min(e_b - win.lo);
        // the model's own facts
        assert_eq!(e_a, e_b + off + row.s, "s_raw = e_A - e_B");
        if row.off { assert!(e_b + e_ca <= 256, "spare bit on off = 1 rows"); }
        assert!(e_ca <= e_cb, "division row: bl(ca) <= bl(cb)");
        if terminal { assert_eq!(e_b, 1); assert!(row.off == false); }
    }
    // ---- expected ---------------------------------------------------------
    let mut expect = ring_lsb(&row.a_new, &row.cb);
    expect.extend(ring_lsb(&row.b, &row.ca));
    expect.extend(bits_of(sched.reb_v(e_a_new), EXP_BITS));
    expect.extend(bits_of(sched.reb_c(e_cb), EXP_BITS));
    expect.extend(bits_of(sched.reb_v(e_b), EXP_BITS));
    expect.extend(bits_of(sched.reb_c(e_ca), EXP_BITS));
    expect.extend(bits_u512(&q_new, wq));
    expect.extend(bits_of(0, SROT));
    expect.push(false);
    expect.push(true);
    expect.push(false);
    Shot { data, expect, check: on_support }
}

/// Forward on the shots (values checked where `check`), then backward on the
/// outputs must restore the data. Returns (T fwd, T inv).
fn round_trip(sched: &StepWidths, wq: usize, with_term: bool, shots: &[Shot], label: &str, cnt: &mut Counts) -> (Harness, Harness) {
    let fwd = build(sched, wq, with_term, false);
    let inv = build(sched, wq, with_term, true);
    let data: Vec<Vec<bool>> = shots.iter().map(|s| s.data.clone()).collect();
    let out = simulate(&fwd, &data, &format!("{label}-fwd"));
    for (i, (o, s)) in out.iter().zip(shots).enumerate() {
        if s.check {
            if o != &s.expect {
                let first = o.iter().zip(&s.expect).position(|(a, b)| a != b).unwrap();
                panic!(
                    "{label}: forward shot {i} differs (step {} W_A {} W_c {} lo_B {} rb {} zone {} first bad wire {first} of {}: r1 0..257, r2 257..514, ex1 514..532, ex2 532..550, q 550..{}, srot, off, gate, term)",
                    sched.step, sched.w_a, sched.w_c, sched.lo_b, sched.rb_div, sched.div_zone_start(), o.len(), 550 + wq
                );
            }
        }
    }
    let back = simulate(&inv, &out, &format!("{label}-inv"));
    for (i, (b, s)) in back.iter().zip(shots).enumerate() {
        assert_eq!(b, &s.data, "{label}: backward shot {i} (step {})", sched.step);
    }
    cnt.inverse_checked += shots.len();
    // The additional promised-domain implementation checks every row whose
    // integer value contract holds. Generic off-support/garbage tests above
    // and elsewhere still use the original APIs and are not filtered.
    let valid: Vec<&Shot> = shots.iter().filter(|s| s.check).collect();
    if !valid.is_empty() {
        let sfwd = build_variant(sched, wq, with_term, false, true);
        let sinv = build_variant(sched, wq, with_term, true, true);
        assert!(sfwd.t <= fwd.t && sinv.t <= inv.t);
        assert!(sfwd.scratch <= fwd.scratch && sinv.scratch <= inv.scratch);
        let inputs: Vec<Vec<bool>> = valid.iter().map(|s| s.data.clone()).collect();
        let expected: Vec<Vec<bool>> = valid.iter().map(|s| s.expect.clone()).collect();
        assert_eq!(simulate(&sfwd, &inputs, &format!("{label}-supported-fwd")), expected);
        assert_eq!(simulate(&sinv, &expected, &format!("{label}-supported-inv")), inputs);
        cnt.supported_checked += valid.len();
    }
    (fwd, inv)
}

fn garbage_rows(rng: &mut impl XofReader, n_data: usize, shots: usize) -> Vec<Vec<bool>> {
    (0..shots)
        .map(|_| {
            let mut bytes = vec![0u8; n_data.div_ceil(8)];
            rng.read(&mut bytes);
            (0..n_data).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect()
        })
        .collect()
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

fn fmt_items(items: &BTreeMap<String, usize>) -> String {
    let order = ["D1", "D0", "D3", "D4", "D5", "D6", "D7", "D7b", "D8", "D6p", "D9", "D11", "D10", "D0c", "D12"];
    let mut s = String::new();
    for k in order {
        if let Some(v) = items.get(k) {
            s.push_str(&format!(" {k} {v}"));
        }
    }
    for (k, v) in items {
        if !order.contains(&k.as_str()) {
            s.push_str(&format!(" {k} {v}"));
        }
    }
    s
}

pub(super) fn run() {
    let env = EnvSnapshot::take();
    std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");
    std::env::set_var("MIDQ_MEASURED_DEMUX", "1");
    std::env::remove_var("MIDQ_CHUNKED_PREFIX");
    // D12's clean-prefix chain (the shared `packed::ctz` kernel) is bounded by
    // MIDQ_PACKED_QCAP - active; the harness's live count is ~590 (data) so
    // the default cap (866) leaves the chain whole. `MIDQ_DIVISION_SELFTEST_QCAP=<n>`
    // sets the cap (e.g. 602 = the data wires + 12, the production room at
    // the D12 moment).
    match std::env::var("MIDQ_DIVISION_SELFTEST_QCAP") {
        Ok(v) => std::env::set_var("MIDQ_PACKED_QCAP", v),
        Err(_) => std::env::remove_var("MIDQ_PACKED_QCAP"),
    }
    std::env::remove_var("MIDQ_PACKED_CTZ_ROOM");
    std::env::remove_var("MIDQ_ONEHOT_COHERENT");
    std::env::set_var("TRAILMIX_THIN_CLZ_WINDOW", "78");
    if std::env::var("MIDQ_DIVISION_SELFTEST_THIN").ok().as_deref() == Some("1") {
        std::env::set_var("TRAILMIX_THIN_SCHEDULE", "1");
        std::env::set_var("TRAILMIX_THIN_SEED", "278");
        std::env::set_var("TRAILMIX_THIN_MARGIN", "0");
        std::env::set_var("TRAILMIX_THIN_VALIDATE", "0");
    } else {
        std::env::remove_var("TRAILMIX_THIN_SCHEDULE");
    }
    let term_from = env_usize("MIDQ_PREFIX_TERMINAL_FROM", super::super::p0_shape::DEFAULT_TERMINAL_FROM);
    let inputs = random_inputs();
    let traces: Vec<Vec<Row>> = inputs.iter().map(|&x| trace(x)).collect();
    // Oracle cross-check dump (`MIDQ_DIVISION_SELFTEST_DUMP=<path>`): per input
    // the hex value, the number of division rows, the terminal step and a
    // rolling hash of (step, s, off) over the division rows, to compare with
    // tools/packed_prefix_model.py's pz_prefix on the same inputs.
    if let Ok(path) = std::env::var("MIDQ_DIVISION_SELFTEST_DUMP") {
        use std::io::Write;
        let mut f = std::fs::File::create(&path).expect("dump file");
        for (x, t) in inputs.iter().zip(&traces) {
            let mut h: u64 = 0;
            let mut divs = 0usize;
            let mut term_step = usize::MAX;
            for (step, row) in t.iter().enumerate() {
                if row.kind == Kind::Div {
                    divs += 1;
                    h = h.wrapping_mul(1_000_003).wrapping_add(((step as u64) << 8) | ((row.s as u64) << 1) | u64::from(row.off));
                    if row.terminal() {
                        term_step = step;
                    }
                }
            }
            writeln!(f, "{x:#x} {divs} {term_step} {h}").expect("dump write");
        }
    }
    let mut cnt = Counts { terminal_steps_min: usize::MAX, e_b_min_margin: usize::MAX, ..Counts::default() };
    let mut t_fwd_sum = 0usize;
    let mut t_inv_sum = 0usize;
    let mut t_rows: Vec<String> = Vec::new();
    let report_steps = [0usize, 1, 2, 10, 50, 100, 150, 200, 250, 300, 350, 364, 365, 378, 400, 440, 480, 500, 520, 529];
    let mut circuits = 0usize;
    let mut garbage_seed = Shake256::default();
    garbage_seed.update(b"packed-division-garbage-v1");
    let mut garbage = garbage_seed.finalize_xof();
    let mut max_scratch = 0usize;

    for step in 0..NSTEPS {
        let sched = StepWidths::from_schedule(step);
        let wq = sched.w_q.clamp(1, 1 << SROT);
        let with_term = step >= term_from;
        cnt.zone_cells_max = cnt.zone_cells_max.max(sched.w_a - sched.div_zone_start());
        let mut shots = Vec::with_capacity(NINPUTS);
        for t in &traces {
            let row = &t[step];
            cnt.rows += 1;
            match row.kind {
                Kind::Div => {}
                Kind::MulOnly => { cnt.mul_only += 1; cnt.gate0_rows += 1; }
                Kind::Draining => { cnt.draining += 1; cnt.gate0_rows += 1; if with_term { cnt.draining_term_live += 1; } }
                Kind::Frozen => { cnt.frozen += 1; cnt.gate0_rows += 1; }
                Kind::Idle => { cnt.idle += 1; cnt.gate0_rows += 1; }
            }
            shots.push(shot(row, &sched, wq, with_term, row.kind == Kind::Div, &mut cnt));
        }
        let (fwd, inv) = round_trip(&sched, wq, with_term, &shots, &format!("s{step}"), &mut cnt);
        circuits += 2;
        t_fwd_sum += fwd.t;
        t_inv_sum += inv.t;
        max_scratch = max_scratch.max(fwd.scratch).max(inv.scratch);
        if report_steps.contains(&step) {
            t_rows.push(format!(
                "DIV step {step:3} W_A {:3} W_c {:3} lo_B {:3} zone [{:3},{:3}) rb {} n_w {:2} q {:2} term {}: T fwd {:5} inv {:5} scratch {:2} |{}",
                sched.w_a, sched.w_c, sched.lo_b, sched.div_zone_start(), sched.w_a, sched.rb_div, sched.div_scan_window(), wq,
                u8::from(with_term), fwd.t, inv.t, fwd.scratch, fmt_items(&fwd.items)
            ));
            t_rows.push(format!("DIV step {step:3} scratch per item (wires above the data registers):{}", fmt_items(&fwd.item_scratch)));
        }
        // the division rows with gate = 0 (every 25th step): byte-identical
        if step % 25 == 0 || step == NSTEPS - 1 {
            let shots0: Vec<Shot> = traces
                .iter()
                .filter(|t| t[step].kind == Kind::Div)
                .map(|t| shot(&t[step], &sched, wq, with_term, false, &mut cnt))
                .collect();
            if !shots0.is_empty() {
                cnt.gate0_variant += shots0.len();
                round_trip(&sched, wq, with_term, &shots0, &format!("s{step}-g0"), &mut cnt);
                circuits += 2;
            }
        }
        // garbage round trips (the circuits are exact gate-inverses for ANY input)
        if step % 100 == 0 || step == 378 || step == NSTEPS - 1 {
            let data = garbage_rows(&mut garbage, fwd.ids.len(), 64);
            let out = simulate(&fwd, &data, &format!("s{step}-garbage-fwd"));
            let back = simulate(&inv, &out, &format!("s{step}-garbage-inv"));
            for (i, (b, d)) in back.iter().zip(&data).enumerate() {
                assert_eq!(b, d, "step {step}: garbage inverse shot {i}");
            }
            cnt.garbage_rt += data.len();
        }
    }

    for r in &t_rows {
        eprintln!("{r}");
    }
    eprintln!(
        "PACKED_DIVISION T: sum over {NSTEPS} steps fwd {t_fwd_sum} inv {t_inv_sum} (per step avg fwd {}), max scratch {max_scratch}",
        t_fwd_sum / NSTEPS
    );

    eprintln!("PACKED_DIVISION counts: {cnt:?}");
    // required classes (task / design 10, refuter fix 7)
    assert!(cnt.div_checked >= 64 * 100, "too few checked division rows: {}", cnt.div_checked);
    assert!(cnt.tight > 0, "no tight-packing (R1 gap 0) row");
    assert!(cnt.off1 > 0, "no off = 1 row");
    assert_eq!(cnt.b_one_terminal, NINPUTS, "every input has one terminal division with term live");
    assert!(cnt.b_one_inexact > 0, "no B = 1 inexact division row");
    assert!(cnt.draining_term_live > 0, "no draining row with term live");
    assert!(cnt.frozen > 0, "no frozen row");
    assert!(cnt.mul_only > 0, "no multiply-only row");
    assert_eq!(cnt.idle, 0, "idle rows on the walk");
    assert!(cnt.terminal_steps_min >= term_from, "a terminal division before MIDQ_PREFIX_TERMINAL_FROM");
    assert_eq!(cnt.miss_term_row, 0);
    assert_eq!(cnt.miss_term_window, 0);
    assert_eq!(cnt.miss_residue4 + cnt.miss_residue9, 0, "tie residue below the cascade bottom on the sample");

    // ---- adversarial review cases (division_review_cases.rs): the same
    // schedule and harness, extra inputs and synthetic rows.
    review::run(term_from, &mut cnt, &mut circuits);
    // A padded envelope need not have a random row exactly at its ceiling;
    // the synthetic review deliberately exercises that boundary too.
    assert!(cnt.ea_eq_wa_off0 > 0, "no e_A = W_A, off = 0 row, including synthetic review");

    // ---- the production route's knobs (LOWQ_ONE_A_ELIM, LOWQ_COMPACT_KGANC,
    // MIDQ_MEASURE_GATE_AND, MIDQ_PREFIX_QCAP=974, MIDQ_DIRECT_CTZ, ...) with
    // MIDQ_CHUNKED_PREFIX forced off (aligned_scan refuses it with the zero
    // layer) and TRAILMIX_THIN_VALIDATE=0 (no 500k-draw validation): the same
    // rows at a few steps, values + inverse + garbage, T printed.
    {
        let route_env = EnvSnapshot::take();
        crate::point_add::trailmix_port::configure_sub1000_trailmix_route();
        std::env::set_var("MIDQ_CHUNKED_PREFIX", "0");
        std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");
        std::env::set_var("TRAILMIX_THIN_VALIDATE", "0");
        std::env::set_var("TRAILMIX_THIN_SCHEDULE", "0");
        let mut route_rows = 0usize;
        for &step in &[0usize, 100, 250, 378, 480, 529] {
            let sched = StepWidths::from_schedule(step);
            let wq = sched.w_q.clamp(1, 1 << SROT);
            let with_term = step >= term_from;
            let shots: Vec<Shot> = traces.iter().map(|t| shot(&t[step], &sched, wq, with_term, t[step].kind == Kind::Div, &mut cnt)).collect();
            let (fwd, inv) = round_trip(&sched, wq, with_term, &shots, &format!("route-s{step}"), &mut cnt);
            let data = garbage_rows(&mut garbage, fwd.ids.len(), 64);
            let out = simulate(&fwd, &data, &format!("route-s{step}-garbage-fwd"));
            let back = simulate(&inv, &out, &format!("route-s{step}-garbage-inv"));
            for (i, (b, d)) in back.iter().zip(&data).enumerate() {
                assert_eq!(b, d, "route step {step}: garbage inverse shot {i}");
            }
            cnt.garbage_rt += data.len();
            route_rows += shots.len();
            circuits += 2;
            eprintln!(
                "DIV route step {step:3} W_A {:3} q {:2} term {}: T fwd {:5} inv {:5} scratch {:2} |{}",
                sched.w_a, wq, u8::from(with_term), fwd.t, inv.t, fwd.scratch, fmt_items(&fwd.items)
            );
        }
        route_env.restore();
        eprintln!("PACKED_DIVISION route pass: {route_rows} rows at 6 steps under configure_sub1000_trailmix_route");
    }
    eprintln!(
        "PACKED_DIVISION PASS: {} rows x {NSTEPS} steps ({} division rows, {} value-checked, {} gate-0 rows, {} gate-0 variants, {} garbage), {} inverses, {circuits} circuits",
        NINPUTS, cnt.div_rows, cnt.div_checked, cnt.gate0_rows, cnt.gate0_variant, cnt.garbage_rt, cnt.inverse_checked
    );
    eprintln!("PACKED_DIVISION_SUPPORTED PASS {} rows, both directions/phase/every reset; generic garbage tests unchanged", cnt.supported_checked);
    env.restore();
}
