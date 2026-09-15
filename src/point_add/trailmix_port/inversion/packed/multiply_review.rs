//! Adversarial review harness for the packed multiply (`multiply.rs`, design
//! 3.2 M1-M12), added by the 2026-09-14 review. It does NOT reuse
//! `multiply_selftest.rs` (an independent packing of the state, an
//! independent support predicate, its own shot generator) and adds what the
//! author's harness does not run:
//!
//! * the BACKWARD direction (`multiply_backward`) on every row: from the
//!   model's post-row state back to the pre-row state, and the forward +
//!   backward ROUND TRIP on the pre-row state (identity), each also with
//!   `gate = 0`;
//! * the round trip on rows OFF the support (model rows the static envelope
//!   rejects) and on fully random garbage states with `gate = 1`: every item
//!   is a permutation with an exact gate-inverse, so the trip must be the
//!   identity whatever the row holds (the design's "a missed row corrupts
//!   only its own exponent and is undone by the backward pass");
//! * more inputs (256) at the widest steps 284-313 (the q = 29 band) and
//!   378-413 (the adder-moment band, all >= 365);
//! * inputs whose terminal step lies in [365, 400] (sampled from the model):
//!   every multiply row of theirs from step 330 on, i.e. the draining rows
//!   (A = 0, B = 1) at the first terminal-aware rows;
//! * synthetic rows for A at the envelope (`e_A = e_B = W_B`, A < B of full
//!   length), R1 gap 0 with A at the envelope, `s2 = s2_bound` WITH a carry
//!   (`D = s2_bound + 1`, the extra M11 layer), the maximal M1 gap (31) at
//!   every `e_B` class, `e_cb = W_c` with `ca_old` dense, B all ones with its
//!   bits inside the coefficient ring, `ca_old` with all-ones low `s2` bits
//!   (the wrapped ring-bottom bits are ones) and a carry;
//! * the coherent engine (`MIDQ_ONEHOT_COHERENT=1`) through the whole
//!   multiply, both directions;
//! * the production route's environment for the ladders and the 9-bit
//!   compare (`LOWQ_COMPACT_KGANC`, `LOWQ_ONE_A_ELIM`, `MIDQ_CHUNK_COMPARE` +
//!   `MIDQ_VARIABLE_CHUNKS` + `MIDQ_MEASURE_COMPARE`, `MIDQ_MEASURED_DEMUX`,
//!   the measured predicates), which the author's harness leaves unset and
//!   the driver selftest sets only partly (no `MIDQ_CHUNK_COMPARE`);
//! * the production THIN schedule (`TRAILMIX_THIN_SCHEDULE=1`, seed 278,
//!   clz window 78 = the driver selftest's configuration): the wide-step and
//!   late-terminator cases again under `reg_los = W - 78`, unless
//!   `MIDQ_MULREV_NO_THIN=1` (the schedule takes ~20 s to generate; the
//!   process-wide cache means an earlier thin schedule of this process is
//!   reused).
//!
//! Toffoli: forward and backward counted separately (CCX + CCZ over the
//! multiply's ops) and asserted equal (gate-for-gate mirror); at the design's
//! step-378 envelope (W_A 76, W_c 256, lo_c 178, q 28) the forward count is
//! asserted within 25% of the design table's itemised sum (6,893 with the
//! refuter deltas). Run alone with `MIDQ_PACKED_SELFTEST=1
//! MIDQ_PACKED_SELFTEST_ONLY=multiply_review`.

use super::multiply::{multiply_backward_marked, multiply_forward_marked};
use super::sched::{StepWidths, EXP_BITS, RING, WINDOW};
use crate::circuit::{analyze_ops, Op, OperationType, QubitId, NO_QUBIT};
use crate::point_add::trailmix_port::circuit::Circuit;
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const NSTEPS: usize = 530;
const SROT: usize = 5;
const SYNTH: usize = usize::MAX;
/// The design table's itemised multiply at step 378 with the refuter deltas.
const DESIGN_T_378: usize = 6893;

fn p() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}
fn bl(x: &U512) -> usize {
    x.bit_len()
}
fn one() -> U512 {
    U512::from(1u64)
}
fn pow2(w: usize) -> U512 {
    one() << w
}

#[derive(Clone)]
struct Row {
    step: usize,
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: U512,
    /// `Some(s2)` on a multiply row.
    s2: Option<usize>,
}

impl Row {
    fn ca_new(&self) -> U512 {
        self.ca + (self.cb << self.s2.expect("multiply row"))
    }
    fn carry(&self) -> usize {
        usize::from(bl(&self.ca_new()) > bl(&self.cb) + self.s2.expect("multiply row"))
    }
    fn gap2(&self) -> usize {
        RING - bl(&self.b) - bl(&self.ca)
    }
}

struct Trace {
    rows: Vec<Row>,
    /// First frozen row (A = 0, q = 0 at the row start).
    term_step: Option<usize>,
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) with every row's pre-state.
fn trace(x_orig: U512) -> Trace {
    let p = p();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, one(), U512::ZERO);
    let mut rows = Vec::with_capacity(NSTEPS);
    let mut term_step = None;
    for step in 0..NSTEPS {
        debug_assert!(a * cb + b * (ca + q * cb) == p, "row invariant");
        let frozen = a.is_zero() && b == one() && q.is_zero();
        if frozen && term_step.is_none() {
            term_step = Some(step);
        }
        let mut s2 = None;
        if !frozen {
            if a < b && !q.is_zero() {
                let t = q.trailing_zeros();
                s2 = Some(t);
                rows.push(Row { step, a, b, ca, cb, q, s2 });
                q ^= one() << t;
                ca += cb << t;
            } else {
                rows.push(Row { step, a, b, ca, cb, q, s2 });
            }
            if ca < cb {
                let mut s = bl(&a) as i64 - bl(&b) as i64;
                if s >= 0 && a < (b << (s as usize)) {
                    s -= 1;
                }
                if s >= 0 {
                    let bsh = b << (s as usize);
                    if a >= bsh {
                        a -= bsh;
                        q ^= one() << (s as usize);
                    }
                }
            }
            if q.is_zero() && !a.is_zero() {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut ca, &mut cb);
            }
        } else {
            rows.push(Row { step, a, b, ca, cb, q, s2 });
        }
    }
    Trace { rows, term_step }
}

fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}
fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}
fn bits_of_u(v: &U512, n: usize) -> Vec<bool> {
    assert!(bl(v) <= n, "value of {} bits in a {n}-wire register", bl(v));
    (0..n).map(|i| v.bit(i)).collect()
}

/// Data wires: [r1(257) | r2(257) | ex1 = e_A,e_cb (18) | ex2 = e_B,e_ca (18) | q(wq) | s_rot(5) | off | gate].
fn state(a: &U512, b: &U512, ca: &U512, cb: &U512, q: &U512, wq: usize, gate: bool) -> Vec<bool> {
    let mut v = ring_lsb(a, cb);
    v.extend(ring_lsb(b, ca));
    v.extend(bits_of(bl(a), EXP_BITS));
    v.extend(bits_of(bl(cb), EXP_BITS));
    v.extend(bits_of(bl(b), EXP_BITS));
    v.extend(bits_of(bl(ca), EXP_BITS));
    v.extend(bits_of_u(q, wq));
    v.extend(bits_of(0, SROT));
    v.push(false);
    v.push(gate);
    v
}

fn rnd_below(rng: &mut impl XofReader, n: U512) -> U512 {
    assert!(!n.is_zero());
    let mut bytes = [0u8; 64];
    rng.read(&mut bytes[..40]);
    U512::from_le_bytes(bytes) % n
}
fn rnd_bl(rng: &mut impl XofReader, w: usize, dense: bool) -> U512 {
    if w == 0 {
        return U512::ZERO;
    }
    if dense {
        return pow2(w) - one();
    }
    pow2(w - 1) + rnd_below(rng, pow2(w - 1))
}
fn rnd_usize(rng: &mut impl XofReader, n: usize) -> usize {
    let mut b = [0u8; 4];
    rng.read(&mut b);
    (u32::from_le_bytes(b) as usize) % n.max(1)
}

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

fn peak_scratch(ops: &[Op], data: &[QubitId]) -> usize {
    let data: std::collections::HashSet<u64> = data.iter().map(|q| q.0).collect();
    let mut live: std::collections::HashSet<u64> = Default::default();
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Dir {
    Fwd,
    Bwd,
    Round,
}

struct Harness {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    t_fwd: usize,
    t_bwd: usize,
    scratch: usize,
    items: Vec<(&'static str, usize)>,
    wq: usize,
    dir: Dir,
}

fn build(sched: &StepWidths, wq: usize, dir: Dir) -> Harness {
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("r1", RING);
    let r2 = c.alloc_qreg_bits("r2", RING);
    let ex1 = c.alloc_qreg_bits("ex1", 2 * EXP_BITS);
    let ex2 = c.alloc_qreg_bits("ex2", 2 * EXP_BITS);
    let q = c.alloc_qreg_bits("q", wq);
    let s_rot = c.alloc_qreg_bits("srot", SROT);
    let off = c.alloc_qreg("off");
    let gate = c.alloc_qreg("gate");
    let ids: Vec<QubitId> = [&r1[..], &r2[..], &ex1[..], &ex2[..], &q[..], &s_rot[..], std::slice::from_ref(&off), std::slice::from_ref(&gate)]
        .iter()
        .flat_map(|r| r.iter().map(|q| QubitId(q.id().into())))
        .collect();
    let start = c.b.ops.len();
    let mut marks: Vec<(&'static str, usize)> = Vec::new();
    let mut t_fwd = 0;
    let mut t_bwd = 0;
    if dir != Dir::Bwd {
        multiply_forward_marked(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, sched.step, sched, &mut |c, name| {
            marks.push((name, c.b.ops.len()));
        });
        t_fwd = toffoli(&c.b.ops[start..]);
    }
    if dir != Dir::Fwd {
        let mid = c.b.ops.len();
        let mut m2: Vec<(&'static str, usize)> = Vec::new();
        multiply_backward_marked(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, sched.step, sched, &mut |c, name| {
            m2.push((name, c.b.ops.len()));
        });
        t_bwd = toffoli(&c.b.ops[mid..]);
        if dir == Dir::Bwd {
            marks = m2;
        }
    }
    let scratch = peak_scratch(&c.b.ops[start..], &ids);
    let items = marks.windows(2).map(|w| (w[0].0, toffoli(&c.b.ops[w[0].1..w[1].1]))).collect();
    Harness { ops: c.b.ops.clone(), ids, t_fwd, t_bwd, scratch, items, wq, dir }
}

/// Up to 64 shots through `h`; checks every reset, phase 0, every non-data
/// qubit 0; returns the data wires per shot.
fn simulate(h: &Harness, shots: &[Vec<bool>], label: &str) -> Vec<Vec<bool>> {
    assert!(!shots.is_empty() && shots.len() <= 64, "{label}: {} shots", shots.len());
    let (nq, nb, _, _) = analyze_ops(h.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-multiply-review-sim-v1");
    seed.update(label.as_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for (shot, data) in shots.iter().enumerate() {
        assert_eq!(data.len(), h.ids.len(), "{label}: shot width");
        for (i, &id) in h.ids.iter().enumerate() {
            if data[i] {
                *sim.qubit_mut(id) |= 1u64 << shot;
            }
        }
    }
    let mask = u64::MAX >> (64 - shots.len());
    super::super::predicate_clear_selftest::checked_apply(&mut sim, &h.ops, mask);
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

struct Shot {
    data: Vec<bool>,
    expect: Vec<bool>,
}

fn diff_report(o: &[bool], e: &[bool], wq: usize) -> String {
    let names = ["r1", "r2", "ex1", "ex2", "q", "srot", "off", "gate"];
    let widths = [RING, RING, 2 * EXP_BITS, 2 * EXP_BITS, wq, SROT, 1, 1];
    let mut at = 0;
    let mut s = String::new();
    for (n, w) in names.iter().zip(widths) {
        let got: Vec<usize> = (0..w).filter(|&k| o[at + k] != e[at + k]).collect();
        if !got.is_empty() {
            s.push_str(&format!(" {n}@{got:?}"));
        }
        at += w;
    }
    s
}

fn run_batch(h: &Harness, shots: &[Shot], label: &str) {
    for chunk in shots.chunks(64) {
        let data: Vec<Vec<bool>> = chunk.iter().map(|s| s.data.clone()).collect();
        let out = simulate(h, &data, label);
        for (i, (o, s)) in out.iter().zip(chunk).enumerate() {
            assert!(o == &s.expect, "{label} [{:?}]: shot {i} differs:{}", h.dir, diff_report(o, &s.expect, h.wq));
        }
    }
}

/// Independent statement of what the circuit needs of a multiply row at the
/// step's envelope (each a theorem T, a width/lo miss W or the two new miss
/// kinds of design section 8).
fn support(row: &Row, s: &StepWidths, wq: usize) -> Result<(), &'static str> {
    let s2 = row.s2.ok_or("not a multiply row")?;
    let (e_a, e_b, e_ca, e_cb) = (bl(&row.a), bl(&row.b), bl(&row.ca), bl(&row.cb));
    let ca_new = row.ca_new();
    let carry = row.carry();
    let d = s2 + carry;
    let lo_c = s.m10_cascade_lo(); // M10's cascade bottom (the tie residue window)
    let checks: [(bool, &'static str); 17] = [
        (row.a < row.b, "gate: A >= B"),
        (!row.q.is_zero() && row.q.trailing_zeros() == s2, "gate: q"),
        (e_a <= s.w_a, "W: e_A > W_A"),
        (e_b >= s.m1_lo_b().max(1) && e_b <= s.w_b, "W: e_B outside [lo_B + 1, W_B]"),
        (e_cb >= s.lo_cb + 1 && e_cb <= s.w_c, "W: e_cb outside [lo_cb + 1, W_c]"),
        (e_ca <= s.w_c, "W: e_ca > W_c"),
        (bl(&ca_new) <= s.w_c, "W: bl(ca_new) > W_c (ca_post)"),
        (bl(&ca_new) == e_cb + d && carry <= 1, "T: bl(ca_new) = e_cb + s2 + carry"),
        (row.ca < (row.cb << s2), "T: ca_old < cb << s2"),
        (e_b + bl(&ca_new) <= RING, "T: e_B + bl(ca_new) <= 257"),
        (e_a + e_cb <= RING, "T: e_A + e_cb <= 257"),
        (row.ca.is_zero() || row.gap2() < WINDOW, "gap_bound"),
        (s2 <= s.s2_bound, "W: s2 > s2_bound"),
        (d < (1 << SROT), "W: s2 + carry >= 32 (shift word)"),
        (bl(&row.q) <= wq, "W: q wider than its register"),
        (bl(&row.q) <= s.w_q.max(1), "W: q wider than the envelope"),
        ((((ca_new >> d) >> lo_c) < (row.cb >> lo_c)) == (carry == 1), "narrow_lt: M10 window tie"),
    ];
    for (ok, why) in checks {
        if !ok {
            return Err(why);
        }
    }
    Ok(())
}

fn pre_state(row: &Row, wq: usize, gate: bool) -> Vec<bool> {
    state(&row.a, &row.b, &row.ca, &row.cb, &row.q, wq, gate)
}
fn post_state(row: &Row, wq: usize, gate: bool) -> Vec<bool> {
    let s2 = row.s2.expect("multiply row");
    let q_new = row.q ^ (one() << s2);
    state(&row.a, &row.b, &row.ca_new(), &row.cb, &q_new, wq, gate)
}

fn shot(row: &Row, wq: usize, dir: Dir, gate: bool) -> Shot {
    match (dir, gate) {
        (Dir::Fwd, true) => Shot { data: pre_state(row, wq, true), expect: post_state(row, wq, true) },
        (Dir::Bwd, true) => Shot { data: post_state(row, wq, true), expect: pre_state(row, wq, true) },
        (Dir::Round, true) => Shot { data: pre_state(row, wq, true), expect: pre_state(row, wq, true) },
        (Dir::Bwd, false) => Shot { data: post_state(row, wq, false), expect: post_state(row, wq, false) },
        (_, false) => Shot { data: pre_state(row, wq, false), expect: pre_state(row, wq, false) },
    }
}

#[derive(Default)]
struct Counts {
    rows: usize,
    off: std::collections::BTreeMap<&'static str, usize>,
    q_over_env: usize,
    draining: usize,
    term_rows: usize,
    carry: usize,
    e_a_at_w_a: usize,
    e_a_at_w_b: usize,
    gap1_zero: usize,
    tight_r2: usize,
    s2_max: usize,
    gap2_max: usize,
    first_mul_hi: usize,
    first_mul_lo: usize,
    b_in_ring: usize,
    round_off: usize,
    garbage: usize,
    steps: std::collections::BTreeSet<usize>,
    shots: usize,
}

impl Counts {
    fn classify(&mut self, row: &Row, s: &StepWidths) {
        let (e_a, e_b, e_ca, e_cb) = (bl(&row.a), bl(&row.b), bl(&row.ca), bl(&row.cb));
        let s2 = row.s2.unwrap();
        self.rows += 1;
        self.steps.insert(row.step);
        if row.a.is_zero() {
            self.draining += 1;
        }
        if row.step >= 365 && row.step != SYNTH {
            self.term_rows += 1;
        }
        if row.carry() == 1 {
            self.carry += 1;
        }
        if e_a == s.w_a {
            self.e_a_at_w_a += 1;
        }
        if e_a == s.w_b {
            self.e_a_at_w_b += 1;
        }
        if e_a + e_cb == RING {
            self.gap1_zero += 1;
        }
        if e_b + s2 + e_cb == RING {
            self.tight_r2 += 1;
        }
        self.s2_max = self.s2_max.max(s2);
        if e_ca == 0 {
            if e_b >= 226 {
                self.first_mul_hi += 1;
            } else {
                self.first_mul_lo += 1;
            }
        } else {
            self.gap2_max = self.gap2_max.max(row.gap2());
        }
        if e_b > RING - 1 - s.w_c {
            self.b_in_ring += 1;
        }
    }
}

/// Every model multiply row of `traces` at `step`, on the support: forward,
/// backward and round trip with gate 1 and gate 0; off-support rows: round
/// trip only (gate 1). Returns the number of active rows run.
fn run_step(traces: &[Trace], step: usize, cnt: &mut Counts, tag: &str, verbose: bool) -> usize {
    let s = StepWidths::from_schedule(step);
    let rows: Vec<&Row> = traces.iter().map(|t| &t.rows[step]).filter(|r| r.s2.is_some()).collect();
    if rows.is_empty() {
        return 0;
    }
    let need = rows.iter().map(|r| bl(&r.q)).max().unwrap();
    let wq = s.w_q.max(need).max(1);
    let on: Vec<&Row> = rows.iter().copied().filter(|r| support(r, &s, wq).is_ok()).collect();
    let off: Vec<&Row> = rows.iter().copied().filter(|r| support(r, &s, wq).is_err()).collect();
    for r in &rows {
        if bl(&r.q) > s.w_q {
            cnt.q_over_env += 1;
        }
    }
    for r in &off {
        *cnt.off.entry(support(r, &s, wq).err().unwrap()).or_insert(0) += 1;
        if verbose {
            eprintln!(
                "PACKED_MULREV {tag} off-support row at step {step}: {} (e_A {} e_B {} e_ca {} e_cb {} s2 {} carry {})",
                support(r, &s, wq).err().unwrap(),
                bl(&r.a),
                bl(&r.b),
                bl(&r.ca),
                bl(&r.cb),
                r.s2.unwrap(),
                r.carry()
            );
        }
    }
    let hf = build(&s, wq, Dir::Fwd);
    let hb = build(&s, wq, Dir::Bwd);
    let hr = build(&s, wq, Dir::Round);
    assert_eq!(hf.t_fwd, hb.t_bwd, "step {step}: forward and backward Toffoli differ ({} vs {})", hf.t_fwd, hb.t_bwd);
    for r in &on {
        cnt.classify(r, &s);
    }
    for (h, dir) in [(&hf, Dir::Fwd), (&hb, Dir::Bwd), (&hr, Dir::Round)] {
        for gate in [true, false] {
            let shots: Vec<Shot> = on.iter().map(|r| shot(r, wq, dir, gate)).collect();
            if !shots.is_empty() {
                cnt.shots += shots.len();
                run_batch(h, &shots, &format!("{tag}-s{step}-{dir:?}-g{}", u8::from(gate)));
            }
        }
    }
    if !off.is_empty() {
        let shots: Vec<Shot> = off.iter().map(|r| shot(r, wq, Dir::Round, true)).collect();
        cnt.round_off += shots.len();
        cnt.shots += shots.len();
        run_batch(&hr, &shots, &format!("{tag}-s{step}-round-offsupport"));
    }
    on.len()
}

/// Random garbage states (gate = 1) through the round trip at `step`.
fn run_garbage(rng: &mut impl XofReader, step: usize, cnt: &mut Counts, tag: &str) {
    let s = StepWidths::from_schedule(step);
    let wq = s.w_q.max(1);
    let hr = build(&s, wq, Dir::Round);
    let mut shots = Vec::new();
    for _ in 0..64 {
        let mut v: Vec<bool> = Vec::with_capacity(hr.ids.len());
        let mut bytes = vec![0u8; hr.ids.len()];
        rng.read(&mut bytes);
        for (i, b) in bytes.iter().enumerate() {
            v.push(b & 1 == 1 && i < hr.ids.len() - SROT - 2);
        }
        let n = v.len();
        // s_rot = 0, off = 0 (the multiply's PRE), gate = 1
        for k in 0..SROT + 1 {
            v[n - 2 - k] = false;
        }
        v[n - 1] = true;
        shots.push(Shot { data: v.clone(), expect: v });
    }
    cnt.garbage += shots.len();
    cnt.shots += shots.len();
    run_batch(&hr, &shots, &format!("{tag}-s{step}-garbage"));
}

/// Synthetic multiply row (the model's own terms), or None when unrealisable.
struct Spec {
    e_a: Option<usize>,
    e_b: usize,
    e_cb: usize,
    s2: usize,
    carry: bool,
    ca_zero: bool,
    gap: Option<usize>,
    dense_a: bool,
    b_ones: bool,
    ca_low_ones: bool,
    cb_dense: bool,
}

fn synth(rng: &mut impl XofReader, s: &StepWidths, wq: usize, sp: &Spec) -> Option<Row> {
    if sp.e_b == 0 || sp.e_cb == 0 || wq < sp.s2 + 1 {
        return None;
    }
    let b = if sp.b_ones { pow2(sp.e_b) - one() } else { rnd_bl(rng, sp.e_b, false) };
    let mut cb = rnd_bl(rng, sp.e_cb, sp.cb_dense);
    if sp.carry && cb == pow2(sp.e_cb - 1) {
        if sp.e_cb == 1 {
            return None;
        }
        cb += one();
    }
    let ca = if sp.ca_zero {
        if sp.carry {
            return None;
        }
        U512::ZERO
    } else {
        // ca_old >> s2 in [lo, cb): lo = 2^e_cb - cb for a carry, else 1
        let lo = if sp.carry { pow2(sp.e_cb) - cb } else { one() };
        // no carry: (ca_old >> s2) + cb < 2^e_cb, i.e. ca_old >> s2 < 2^e_cb - cb
        let hi_nc = if sp.carry { cb } else { cb.min(pow2(sp.e_cb) - cb) };
        let (lo, hi) = match sp.gap {
            Some(g) => {
                let bl_ca = RING.checked_sub(sp.e_b + g)?;
                let hb = bl_ca.checked_sub(sp.s2)?;
                if hb == 0 {
                    return None;
                }
                (lo.max(pow2(hb - 1)), hi_nc.min(pow2(hb)))
            }
            None => (lo, hi_nc),
        };
        if lo >= hi {
            return None;
        }
        let hi_part = lo + rnd_below(rng, hi - lo);
        let low = if sp.s2 == 0 {
            U512::ZERO
        } else if sp.ca_low_ones {
            pow2(sp.s2) - one()
        } else {
            rnd_below(rng, pow2(sp.s2))
        };
        (hi_part << sp.s2) + low
    };
    let e_a = sp.e_a.unwrap_or_else(|| rnd_usize(rng, sp.e_b.min(s.w_a).min(RING - sp.e_cb) + 1));
    let a = if e_a == 0 {
        U512::ZERO
    } else if e_a < sp.e_b {
        rnd_bl(rng, e_a, sp.dense_a)
    } else if e_a == sp.e_b {
        if sp.dense_a {
            if b == pow2(e_a - 1) {
                return None;
            }
            b - one()
        } else {
            let lo = pow2(e_a - 1);
            if lo >= b {
                return None;
            }
            lo + rnd_below(rng, b - lo)
        }
    } else {
        return None;
    };
    let room = wq - sp.s2 - 1;
    let r = if room == 0 { U512::ZERO } else { rnd_below(rng, pow2(room)) };
    let q = (r << (sp.s2 + 1)) | (one() << sp.s2);
    let row = Row { step: SYNTH, a, b, ca, cb, q, s2: Some(sp.s2) };
    if support(&row, s, wq).is_err() || (row.carry() == 1) != sp.carry {
        return None;
    }
    Some(row)
}

fn specs_for(s: &StepWidths, wq: usize) -> Vec<(&'static str, Spec)> {
    let s2b = s.s2_bound.min((1 << SROT) - 2).min(wq.saturating_sub(1));
    let clamp_b = |e: i64| -> usize { e.clamp((s.lo_b + 1) as i64, s.w_b as i64) as usize };
    let clamp_cb = |e: i64| -> usize { e.clamp((s.lo_cb + 1) as i64, s.w_c as i64) as usize };
    let mid_cb = (s.lo_cb + 1 + s.w_c) / 2;
    let base = |e_b: usize, e_cb: usize, s2: usize, carry: bool| Spec {
        e_a: None,
        e_b,
        e_cb,
        s2,
        carry,
        ca_zero: false,
        gap: None,
        dense_a: false,
        b_ones: false,
        ca_low_ones: false,
        cb_dense: false,
    };
    // e_B leaving room for bl(ca_new) = e_cb + s2 + carry plus a small gap
    let eb_for = |e_cb: usize, s2: usize, carry: bool, gap: usize| -> usize {
        clamp_b(RING as i64 - e_cb as i64 - s2 as i64 - i64::from(carry) - gap as i64)
    };
    let mut v = Vec::new();
    // A at the envelope: e_A = e_B = W_B (A < B, both full width), carry 0 / 1, A dense;
    // at late steps lo_cb + 1 + W_B is close to 257, so s2 is small
    {
        let s2 = 1usize.min(s2b);
        let e_cb = clamp_cb(RING as i64 - s.w_b as i64 - s2 as i64 - 1);
        v.push(("eA_top", Spec { e_a: Some(s.w_b), ..base(s.w_b, e_cb, s2, false) }));
        let e_cb = clamp_cb(RING as i64 - s.w_b as i64 - s2 as i64 - 2);
        v.push(("eA_top_carry", Spec { e_a: Some(s.w_b), ..base(s.w_b, e_cb, s2, true) }));
        v.push(("eA_top_dense", Spec { e_a: Some(s.w_b), dense_a: true, b_ones: true, ..base(s.w_b, e_cb, s2, true) }));
        // R1 gap 0 with A at the envelope: e_cb = 257 - W_B (forces s2 = 0, carry 0)
        let e_cb = RING - s.w_b;
        if e_cb >= s.lo_cb + 1 && e_cb <= s.w_c {
            v.push(("eA_top_gap1_zero", Spec { e_a: Some(s.w_b), dense_a: true, ..base(s.w_b, e_cb, 0, false) }));
            v.push(("eA_top_gap1_zero_ca0", Spec { e_a: Some(s.w_b), dense_a: true, ca_zero: true, ..base(s.w_b, e_cb, 0, false) }));
        }
    }
    // s2 = s2_bound with a carry: D = s2_bound + 1 (M11's extra layer)
    {
        let e_cb = clamp_cb(s.w_c as i64 - s2b as i64 - 1);
        v.push(("s2max_carry", base(eb_for(e_cb, s2b, true, 4), e_cb, s2b, true)));
        v.push(("s2max_carry_lowones", Spec { ca_low_ones: true, cb_dense: true, ..base(eb_for(e_cb, s2b, true, 4), e_cb, s2b, true) }));
        v.push(("s2max_nocarry", base(eb_for(e_cb, s2b, false, 4), e_cb, s2b, false)));
    }
    // maximal M1 gap 31, at low / mid / high e_B; and 25 with a carry.
    // bl(ca_old) = 257 - e_B - 31 = e_cb + s2 forces a carry (bl(ca_old >> s2) =
    // e_cb and bl(cb) = e_cb sum past 2^e_cb); the no-carry form has
    // bl(ca_old) = e_cb + s2 - 1.
    for (name, e_b_hint, carry) in [
        ("gap31_eb_lo", s.lo_b + 1, true),
        ("gap31_eb_mid", (s.lo_b + 1 + s.w_b) / 2, true),
        ("gap31_eb_mid_nocarry", (s.lo_b + 1 + s.w_b) / 2, false),
        ("gap31_eb_hi", s.w_b, false),
    ] {
        let e_b = clamp_b(e_b_hint as i64);
        let bl_ca = RING as i64 - e_b as i64 - (WINDOW as i64 - 1);
        let e_cb = clamp_cb(bl_ca - s2b as i64 / 3 + i64::from(!carry));
        let s2 = (bl_ca - e_cb as i64 + i64::from(!carry)).max(0) as usize;
        v.push((name, Spec { gap: Some(WINDOW - 1), ..base(e_b, e_cb, s2, carry) }));
    }
    {
        let e_b = clamp_b((s.lo_b + 1 + s.w_b) as i64 / 2);
        let bl_ca = RING as i64 - e_b as i64 - 25;
        let e_cb = clamp_cb(bl_ca - s2b as i64 / 3);
        let s2 = (bl_ca - e_cb as i64).max(0) as usize;
        v.push(("gap25_carry", Spec { gap: Some(25), ..base(e_b, e_cb, s2, true) }));
    }
    // ring bottom: e_cb = W_c (s2 = 0, carry 0; ca_old < 2^W_c - cb), A dense
    v.push(("ring_bottom", Spec { dense_a: true, ..base(eb_for(s.w_c, 0, false, 2), s.w_c, 0, false) }));
    // M1 window wrapping B's low bits ABOVE ca's MSB: e_B > 225 with ca_old != 0
    if s.w_b >= 226 {
        let s2 = 3usize.min(s2b);
        let e_cb = clamp_cb(s.w_c as i64 - s2 as i64 - 2);
        for e_b in [226usize.max(s.lo_b + 1), (226 + s.w_b) / 2, s.w_b] {
            if let Some(g) = RING.checked_sub(e_b + e_cb + s2) {
                if (1..WINDOW).contains(&g) {
                    v.push(("wrap_ca_nonzero", Spec { gap: Some(g), ..base(e_b, e_cb, s2, true) }));
                }
            }
        }
    }
    // B all ones inside the coefficient ring, tight (B's MSB is the absorb wire)
    if RING > mid_cb + s2b / 2 {
        let e_b = RING - mid_cb - s2b / 2;
        if e_b > RING - 1 - s.w_c {
            v.push(("b_ones_in_ring_tight", Spec { b_ones: true, ..base(clamp_b(e_b as i64), mid_cb, s2b / 2, false) }));
        }
    }
    // ca_old low s2 bits all ones (the wrapped bits at the ring bottom) with a carry, cb dense
    v.push(("ca_lowones_carry", Spec { ca_low_ones: true, cb_dense: true, ..base(eb_for(mid_cb, s2b / 2, true, 3), mid_cb, s2b / 2, true) }));
    // draining with the maximal gap and a carry
    v.push(("drain_gap31", Spec { e_a: Some(0), gap: Some(WINDOW - 1), ..base(1, clamp_cb(RING as i64 - 1 - 31 - s2b as i64 / 2), s2b / 2, true) }));
    v.push(("drain_carry_full", Spec { e_a: Some(0), gap: Some(2), ..base(1, clamp_cb(RING as i64 - 1 - 2 - s2b as i64 / 2), s2b / 2, true) }));
    // first multiply, e_B just above 225 and at 256
    for e_b in [226usize, 240, 256] {
        if e_b >= s.lo_b + 1 && e_b <= s.w_b {
            v.push(("ca0_wrap", Spec { ca_zero: true, ..base(e_b, clamp_cb(RING as i64 - e_b as i64 - 1), 0, false) }));
        }
    }
    v
}

fn run_synth(rng: &mut impl XofReader, step: usize, cnt: &mut Counts, tag: &str) -> (Vec<&'static str>, Vec<&'static str>) {
    let s = StepWidths::from_schedule(step);
    let wq = s.w_q.max(1);
    let hf = build(&s, wq, Dir::Fwd);
    let hb = build(&s, wq, Dir::Bwd);
    let hr = build(&s, wq, Dir::Round);
    let mut made = Vec::new();
    let mut missing = Vec::new();
    for (name, spec) in specs_for(&s, wq) {
        let mut got = None;
        for _ in 0..24 {
            if let Some(r) = synth(rng, &s, wq, &spec) {
                got = Some(r);
                break;
            }
        }
        let Some(row) = got else {
            missing.push(name);
            continue;
        };
        cnt.classify(&row, &s);
        let label = format!(
            "{tag}-synth-s{step}-{name} (e_A {} e_B {} e_ca {} e_cb {} s2 {} carry {})",
            bl(&row.a),
            bl(&row.b),
            bl(&row.ca),
            bl(&row.cb),
            row.s2.unwrap(),
            row.carry()
        );
        for (h, dir) in [(&hf, Dir::Fwd), (&hb, Dir::Bwd), (&hr, Dir::Round)] {
            let shots = [shot(&row, wq, dir, true), shot(&row, wq, dir, false)];
            cnt.shots += 2;
            run_batch(h, &shots, &label);
        }
        made.push(name);
    }
    (made, missing)
}

struct EnvGuard {
    saved: Vec<(&'static str, Option<std::ffi::OsString>)>,
}
impl EnvGuard {
    fn set(vars: &[(&'static str, Option<&str>)]) -> Self {
        let saved = vars
            .iter()
            .map(|(k, v)| {
                let old = std::env::var_os(k);
                match v {
                    Some(v) => std::env::set_var(k, v),
                    None => std::env::remove_var(k),
                }
                (*k, old)
            })
            .collect();
        EnvGuard { saved }
    }
}
impl Drop for EnvGuard {
    fn drop(&mut self) {
        for (k, v) in self.saved.drain(..).rev() {
            match v {
                Some(v) => std::env::set_var(k, v),
                None => std::env::remove_var(k),
            }
        }
    }
}

fn inputs(seed: &[u8], n: usize) -> Vec<U512> {
    let mut h = Shake256::default();
    h.update(seed);
    let mut xof = h.finalize_xof();
    let p = p();
    (0..n)
        .map(|_| {
            let mut bytes = [0u8; 64];
            xof.read(&mut bytes[..32]);
            let x = U512::from_le_bytes(bytes) % p;
            if x.is_zero() { one() } else { x }
        })
        .collect()
}

const WIDE_STEPS: [std::ops::RangeInclusive<usize>; 2] = [284..=313, 378..=413];

/// The schedule-dependent passes (run once per schedule).
fn passes(sched_name: &str, verbose: bool) -> Counts {
    let mut cnt = Counts::default();
    let t0 = std::time::Instant::now();
    // geometry of the wide steps
    let mut max_s2b = (0usize, 0usize);
    let mut max_wq = (0usize, 0usize);
    let mut d_overflow_steps: Vec<usize> = Vec::new();
    let mut zone_from_lo: usize = 0;
    for step in 0..NSTEPS {
        let s = StepWidths::from_schedule(step);
        if s.s2_bound > max_s2b.0 {
            max_s2b = (s.s2_bound, step);
        }
        if s.w_q > max_wq.0 {
            max_wq = (s.w_q, step);
        }
        assert!(s.w_b - s.m1_lo_b() < 128, "step {step}: M1 needs W_B - lo_B < 128");
        assert!(s.m1_lo_b() + WINDOW <= RING, "step {step}: M1 window passes wire 257");
        // D = s2_bound + 1 must fit the 5-bit shift word and M11's layer count
        if s.s2_bound + 1 >= (1 << SROT.min(s.rb_mul_plus_carry())) {
            d_overflow_steps.push(step);
        }
        if s.lo_cb + 1 < RING - s.w_a {
            zone_from_lo += 1;
        }
    }
    eprintln!(
        "PACKED_MULREV {sched_name}: steps where s2_bound + 1 does not fit the shift word / M11 layers: {:?}; steps where M5's zone edge is lo_cb + 1 (below the design's 257 - W_A): {zone_from_lo}",
        d_overflow_steps
    );
    for step in [284usize, 298, 313, 347, 378, 396, 413] {
        let s = StepWidths::from_schedule(step);
        let h = build(&s, s.w_q.max(1), Dir::Fwd);
        let items: Vec<String> = h.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
        eprintln!("PACKED_MULREV {sched_name} T step {step}: {} (scratch {}) | {}", h.t_fwd, h.scratch, items.join(", "));
        eprintln!(
            "PACKED_MULREV {sched_name} geometry step {step}: W_A {} W_B {} W_c {} wq {} lo_A {} lo_B {} lo_ca {} lo_cb {} s2_bound {} rb {}/{} | M1 ring [{}, {}) | M5 zone [{}, {}) | M10 cells [{}, {})",
            s.w_a,
            s.w_b,
            s.w_c,
            s.w_q,
            s.lo_a,
            s.lo_b,
            s.lo_ca,
            s.lo_cb,
            s.s2_bound,
            s.rb_mul,
            s.rb_mul_plus_carry(),
            s.m1_lo_b(),
            (s.w_b + WINDOW).min(RING),
            s.mul_zone_start(),
            s.mul_window_cells(),
            s.m10_lo_c(),
            s.w_c
        );
    }
    eprintln!("PACKED_MULREV {sched_name}: max s2_bound {} at step {}, max q envelope {} at step {}", max_s2b.0, max_s2b.1, max_wq.0, max_wq.1);

    // ---- wide steps, 256 inputs -----------------------------------------
    let traces: Vec<Trace> = inputs(b"packed-multiply-review-wide-v1", 256).iter().map(|&x| trace(x)).collect();
    let mut wide_rows = 0;
    for range in WIDE_STEPS.iter() {
        for step in range.clone() {
            wide_rows += run_step(&traces, step, &mut cnt, "wide", verbose);
        }
    }
    eprintln!("PACKED_MULREV {sched_name} wide: {wide_rows} active rows over steps 284-313 and 378-413 (256 inputs), {:.1}s", t0.elapsed().as_secs_f64());
    // every other step as well (the wide bands are the peak; the rest is cheap)
    let mut rest_rows = 0;
    let mut rest_cnt = Counts::default();
    for step in (0..NSTEPS).filter(|s| !WIDE_STEPS.iter().any(|r| r.contains(s))) {
        rest_rows += run_step(&traces, step, &mut rest_cnt, "all", verbose);
    }
    let off: Vec<String> = rest_cnt.off.iter().map(|(k, v)| format!("{k}: {v}")).collect();
    eprintln!(
        "PACKED_MULREV {sched_name} all-steps: {rest_rows} more active rows over the remaining {} steps (256 inputs; draining {}, first multiplies e_B>=226 {} / <=225 {}, s2 max {}, gap2 max {}, q over envelope {}, off-support rows {} [{}]), {:.1}s",
        rest_cnt.steps.len(),
        rest_cnt.draining,
        rest_cnt.first_mul_hi,
        rest_cnt.first_mul_lo,
        rest_cnt.s2_max,
        rest_cnt.gap2_max,
        rest_cnt.q_over_env,
        rest_cnt.round_off,
        off.join(", "),
        t0.elapsed().as_secs_f64()
    );
    cnt.shots += rest_cnt.shots;

    // ---- late terminators (terminal step in [365, 400]) ------------------
    let pool: Vec<Trace> = inputs(b"packed-multiply-review-late-v1", 3000).iter().map(|&x| trace(x)).collect();
    let mut hist = [0usize; 6]; // <365, 365-399, 400-439, 440-479, 480-529, none
    for t in &pool {
        let k = match t.term_step {
            Some(s) if s < 365 => 0,
            Some(s) if s < 400 => 1,
            Some(s) if s < 440 => 2,
            Some(s) if s < 480 => 3,
            Some(_) => 4,
            None => 5,
        };
        hist[k] += 1;
    }
    let late: Vec<Trace> = pool.into_iter().filter(|t| matches!(t.term_step, Some(s) if (365..=400).contains(&s))).take(64).collect();
    eprintln!(
        "PACKED_MULREV {sched_name} late: terminal-step histogram of 3000 inputs [<365: {}, 365-399: {}, 400-439: {}, 440-479: {}, 480-529: {}, none: {}]; {} inputs with terminal step in [365, 400] selected (min {:?}, max {:?})",
        hist[0],
        hist[1],
        hist[2],
        hist[3],
        hist[4],
        hist[5],
        late.len(),
        late.iter().filter_map(|t| t.term_step).min(),
        late.iter().filter_map(|t| t.term_step).max()
    );
    assert!(hist[0] == 0, "an input terminated before 365 (term_row miss)");
    assert!(!late.is_empty(), "no input terminates in [365, 400]");
    let mut late_rows = 0;
    for step in 330..NSTEPS {
        late_rows += run_step(&late, step, &mut cnt, "late", verbose);
    }
    eprintln!("PACKED_MULREV {sched_name} late: {late_rows} active rows from step 330 on, {:.1}s", t0.elapsed().as_secs_f64());

    // ---- synthetic classes + garbage round trips ---------------------------
    let mut seed = Shake256::default();
    seed.update(b"packed-multiply-review-synth-v1");
    seed.update(sched_name.as_bytes());
    let mut rng = seed.finalize_xof();
    for step in [284usize, 298, 313, 347, 378, 396, 413, 1, 100, 250, 480] {
        let (made, missing) = run_synth(&mut rng, step, &mut cnt, "synth");
        eprintln!("PACKED_MULREV {sched_name} synth step {step}: {} rows [{}]; unrealisable [{}]", made.len(), made.join(" "), missing.join(" "));
        run_garbage(&mut rng, step, &mut cnt, "garbage");
    }
    cnt
}

fn report(name: &str, cnt: &Counts) {
    let off: Vec<String> = cnt.off.iter().map(|(k, v)| format!("{k}: {v}")).collect();
    eprintln!(
        "PACKED_MULREV {name} classes: active rows {} over {} steps, shots {} | draining {} rows>=365 {} carry {} e_A=W_A {} e_A=W_B {} gap1_zero {} tight_r2 {} s2_max {} gap2_max {} first_mul (e_B>=226 {}, <=225 {}) b_in_ring {} | q over envelope {} | off-support rows (round trip only) {} [{}] | garbage round trips {}",
        cnt.rows,
        cnt.steps.len(),
        cnt.shots,
        cnt.draining,
        cnt.term_rows,
        cnt.carry,
        cnt.e_a_at_w_a,
        cnt.e_a_at_w_b,
        cnt.gap1_zero,
        cnt.tight_r2,
        cnt.s2_max,
        cnt.gap2_max,
        cnt.first_mul_hi,
        cnt.first_mul_lo,
        cnt.b_in_ring,
        cnt.q_over_env,
        cnt.round_off,
        off.join(", "),
        cnt.garbage
    );
}

pub(crate) fn run() {
    let _env = EnvGuard::set(&[
        ("MIDQ_KG_ZERO_LAYER", Some("1")),
        ("MIDQ_CHUNKED_PREFIX", None),
        ("MIDQ_PACKED_CTZ_ROOM", Some("12")),
        ("MIDQ_ONEHOT_COHERENT", None),
    ]);
    let verbose = std::env::var_os("MIDQ_MULREV_VERBOSE").is_some();
    let t0 = std::time::Instant::now();

    // ---- T at the design envelope, forward = backward, within 25% ----------
    {
        let sched = StepWidths::new(378, 76, 76, 256, 28, 0, 0, 178, 178, 31, 31);
        let hf = build(&sched, 28, Dir::Fwd);
        let hb = build(&sched, 28, Dir::Bwd);
        let items: Vec<String> = hf.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
        let items_b: Vec<String> = hb.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
        eprintln!(
            "PACKED_MULREV T design-envelope step 378 (W_A 76, W_c 256, lo_c 178, q 28): forward {} backward {} (design table {DESIGN_T_378}: {:+.1}%), scratch peak {} | fwd {} | bwd {}",
            hf.t_fwd,
            hb.t_bwd,
            100.0 * (hf.t_fwd as f64 - DESIGN_T_378 as f64) / DESIGN_T_378 as f64,
            hf.scratch,
            items.join(", "),
            items_b.join(", ")
        );
        assert_eq!(hf.t_fwd, hb.t_bwd, "forward/backward Toffoli differ at the design envelope");
        let dev = (hf.t_fwd as f64 - DESIGN_T_378 as f64).abs() / DESIGN_T_378 as f64;
        assert!(dev <= 0.25, "multiply T at step 378 deviates {:.1}% from the design table", 100.0 * dev);
    }

    // ---- static schedule ------------------------------------------------------
    let cnt = passes("static", verbose);
    report("static", &cnt);

    // ---- coherent engine through the whole multiply (both directions) --------
    {
        let _g = EnvGuard::set(&[("MIDQ_ONEHOT_COHERENT", Some("1"))]);
        let traces: Vec<Trace> = inputs(b"packed-multiply-review-coherent-v1", 64).iter().map(|&x| trace(x)).collect();
        let mut c2 = Counts::default();
        let mut rows = 0;
        for step in [300usize, 378, 400] {
            rows += run_step(&traces, step, &mut c2, "coherent", verbose);
        }
        let mut seed = Shake256::default();
        seed.update(b"packed-multiply-review-coherent-synth-v1");
        let mut rng = seed.finalize_xof();
        let (made, missing) = run_synth(&mut rng, 378, &mut c2, "coherent");
        run_garbage(&mut rng, 378, &mut c2, "coherent");
        eprintln!(
            "PACKED_MULREV coherent (MIDQ_ONEHOT_COHERENT=1): {rows} model rows at steps 300/378/400 + {} synthetic [{}] (unrealisable [{}]) + 64 garbage, both directions, shots {}",
            made.len(),
            made.join(" "),
            missing.join(" "),
            c2.shots
        );
        assert!(rows > 0);
    }

    // ---- production route environment (ladders, 9-bit compare, demux) -------
    {
        let _g = EnvGuard::set(&[
            ("LOWQ_COMPACT_KGANC", Some("1")),
            ("LOWQ_ONE_A_ELIM", Some("1")),
            ("TRAILMIX_Q_TARGET", Some("685")),
            ("MIDQ_MEASURED_DEMUX", Some("1")),
            ("MIDQ_MEASURE_PREDICATE", Some("1")),
            ("MIDQ_MEASURE_GATE_AND", Some("1")),
            ("MIDQ_MEASURE_COMPARE", Some("1")),
            ("MIDQ_CHUNK_COMPARE", Some("1")),
            ("MIDQ_VARIABLE_CHUNKS", Some("1")),
            ("MIDQ_CHUNK_COMPARE_QCAP", Some("866")),
            ("MIDQ_PREFIX_QCAP", Some("866")),
            ("MIDQ_CHUNKED_PREFIX", Some("0")),
        ]);
        let traces: Vec<Trace> = inputs(b"packed-multiply-review-prod-v1", 64).iter().map(|&x| trace(x)).collect();
        let mut c3 = Counts::default();
        let mut rows = 0;
        for step in [1usize, 100, 300, 378, 400, 480] {
            rows += run_step(&traces, step, &mut c3, "prodenv", verbose);
        }
        let mut seed = Shake256::default();
        seed.update(b"packed-multiply-review-prod-synth-v1");
        let mut rng = seed.finalize_xof();
        let (made, missing) = run_synth(&mut rng, 378, &mut c3, "prodenv");
        run_garbage(&mut rng, 378, &mut c3, "prodenv");
        let s = StepWidths::from_schedule(378);
        let h = build(&s, s.w_q.max(1), Dir::Fwd);
        let items: Vec<String> = h.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
        eprintln!(
            "PACKED_MULREV prod-env (COMPACT_KGANC, ONE_A_ELIM, CHUNK_COMPARE+VARIABLE_CHUNKS+MEASURE_COMPARE, MEASURED_DEMUX, measured predicates): {rows} model rows at 6 steps + {} synthetic (unrealisable [{}]) + 64 garbage, both directions, shots {}; T step 378 {} scratch {} | {}",
            made.len(),
            missing.join(" "),
            c3.shots,
            h.t_fwd,
            h.scratch,
            items.join(", ")
        );
        assert!(rows > 0);
    }

    // ---- the production thin schedule -----------------------------------------
    if std::env::var_os("MIDQ_MULREV_NO_THIN").is_none() {
        let _g = EnvGuard::set(&[
            ("TRAILMIX_THIN_SCHEDULE", Some("1")),
            ("TRAILMIX_THIN_SEED", Some("278")),
            ("TRAILMIX_THIN_MARGIN", Some("0")),
            ("TRAILMIX_THIN_VALIDATE", Some("500000")),
            ("TRAILMIX_THIN_CLZ_WINDOW", Some("78")),
            ("TRAILMIX_SROT_W", Some("5")),
            ("TRAILMIX_COUNTER_W", Some("8")),
        ]);
        let t1 = std::time::Instant::now();
        let s0 = StepWidths::from_schedule(0);
        eprintln!("PACKED_MULREV thin schedule ready ({:.1}s), step 0: W_A {} W_c {} wq {}", t1.elapsed().as_secs_f64(), s0.w_a, s0.w_c, s0.w_q);
        let cnt_thin = passes("thin", verbose);
        report("thin", &cnt_thin);
    } else {
        eprintln!("PACKED_MULREV thin schedule pass skipped (MIDQ_MULREV_NO_THIN)");
    }

    eprintln!(
        "PACKED_MULREV PASS: forward, backward and round trip (gate 1 / gate 0) on every on-support model multiply row of the wide steps 284-313 / 378-413 (256 inputs) and of the late terminators from step 330; round trips on the off-support rows and on garbage; synthetic edge rows; coherent engine; production-route env; value, phase 0, ancillae clean at every reset ({:.0}s)",
        t0.elapsed().as_secs_f64()
    );
}
