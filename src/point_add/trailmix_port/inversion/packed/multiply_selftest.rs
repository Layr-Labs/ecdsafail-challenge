//! Selftest for `multiply_forward` (packed M1-M12) on REAL packed-prefix
//! states: the exact `pz_prefix` recurrence of `tools/packed_prefix_model.py`
//! (single-q Kaliski step, 530 rows) is run in U512 on 64 Shake256-seeded
//! inputs; every multiply row of every input gives one active shot (R1 = [A |
//! gap | cb], R2 = [B | gap | ca_old], the four exponents, q, s_rot = off = 0,
//! gate = 1) at the step's envelope (`StepWidths::from_schedule`, the static
//! tables) and is checked against the model's post-row state: R2 = [B | gap |
//! ca_new], `q ^= 1 << s2`, `e_ca = bl(ca_new)`, everything else untouched,
//! `s_rot` and `off` back to 0, phase 0, every freed ancilla 0 at its reset
//! (`checked_apply`). Every step with at least one multiply row among the
//! inputs is run (up to 530); the other inputs ride along as `gate = 0` filler
//! (their pre-step state must be untouched), and every active batch is rerun
//! with `gate = 0`.
//!
//! Required classes (task / design 10, refuter fix 7), counted and asserted
//! non-empty from the traces or from synthetic rows built in the model's own
//! terms (`synth`): first multiplies with `ca_old = 0` and `e_B in [226, 256]`
//! (B's low bits wrap into M1's window) and with `e_B <= 225` (all-zero window,
//! sentinel); the maximal `s2` of the step's bound (with carry 0, and `s2 =
//! bound - 1` with carry 1 so `D = s2 + 1` fits the shift word); the carry case
//! (`bl(ca_new) = e_cb + s2 + 1`); foreign bits adjacent to the field ends: R1
//! gap 0 (A's MSB one wire below cb's MSB, all-ones A), the tight R2 row
//! `e_B + s2 + e_cb = 257` (B's MSB IS the absorb wire, carry provably 0), R2
//! gap 1 before the multiply (the minimum - gap 0 is impossible, see `specs_for`;
//! ca's MSB at M1's window position 1) and gap 31 (the last window position); the zone edge `e_cb = lo_cb + 1` and the ring
//! bottom `e_cb = W_c`; `e_B = lo_B + 1` and `e_B = W_B` (M1's rotation
//! amounts 1 and max); draining rows (A = 0, B = 1, q != 0); dense (all-ones)
//! A / B / cb / ca low bits; `gate = 0` rows. Prints the measured Toffoli per
//! item at steps 100 / 250 / 378 (and the scratch peak), next to the design's
//! model (`tools/spike/packed_design_tmodel.py`).
//!
//! Environment: `MIDQ_KG_ZERO_LAYER=1` (set here, restored after),
//! `MIDQ_CHUNKED_PREFIX` unset (asserted by the scan), `MIDQ_PACKED_CTZ_ROOM=12`
//! (the design's M2 budget 866 - 854, so the ctz kernel is measured at its
//! production shape rather than with one 32-wire chain).

use super::super::sched::{StepWidths, EXP_BITS, RING, WINDOW};
use super::multiply_forward_marked;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const NSTEPS: usize = 530;
const NINPUTS: usize = 64;
const SROT: usize = 5;
/// `step` marker of a synthetic row.
const SYNTH: usize = usize::MAX;

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

/// One multiply row: the pre-row state and the shift.
#[derive(Clone)]
struct MulRow {
    step: usize,
    a: U512,
    b: U512,
    ca_old: U512,
    cb: U512,
    q: U512,
    s2: usize,
    dense: bool,
}

impl MulRow {
    fn ca_new(&self) -> U512 {
        self.ca_old + (self.cb << self.s2)
    }
    fn carry(&self) -> bool {
        bl(&self.ca_new()) > bl(&self.cb) + self.s2
    }
    fn gap2(&self) -> usize {
        RING - bl(&self.b) - bl(&self.ca_old)
    }
}

/// Any row's pre-step values (gate = 0 filler).
#[derive(Clone)]
struct Pre {
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: U512,
}

struct Trace {
    pre: Vec<Pre>,
    mul: Vec<Option<MulRow>>,
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) with multiply rows recorded.
fn trace(x_orig: U512) -> Trace {
    let p = p();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, U512::from(1u64), U512::ZERO);
    let one = U512::from(1u64);
    let mut pre = Vec::with_capacity(NSTEPS);
    let mut mul = Vec::with_capacity(NSTEPS);
    for step in 0..NSTEPS {
        assert!(a * cb + b * (ca + q * cb) == p, "row invariant");
        pre.push(Pre { a, b, ca, cb, q });
        let mut mrow = None;
        if !(a.is_zero() && b == one && q.is_zero()) {
            if a < b && !q.is_zero() {
                let s2 = q.trailing_zeros();
                mrow = Some(MulRow { step, a, b, ca_old: ca, cb, q, s2, dense: false });
                q ^= one << s2;
                ca += cb << s2;
            }
            if ca < cb {
                let mut s = bl(&a) as i64 - bl(&b) as i64;
                if s >= 0 && a < (b << (s as usize)) {
                    s -= 1;
                }
                if s >= 0 {
                    let s = s as usize;
                    let bsh = b << s;
                    if a >= bsh {
                        a -= bsh;
                        q ^= one << s;
                    }
                }
            }
            if q.is_zero() && !a.is_zero() {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut ca, &mut cb);
            }
        }
        mul.push(mrow);
    }
    assert!(a.is_zero() && q.is_zero(), "input did not terminate by {NSTEPS}");
    Trace { pre, mul }
}

/// LSB-frame ring content: value bits at wires [0, bl v), coefficient bit j at
/// wire 256 - j. Asserts the packing invariant (no overlap).
fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant: bl {} + bl {}", bl(value), bl(coef));
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}

fn bits_of_u(v: &U512, n: usize) -> Vec<bool> {
    assert!(bl(v) <= n, "value of {} bits in a {n}-wire register", bl(v));
    (0..n).map(|i| v.bit(i)).collect()
}

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

/// Random value in `[lo, hi)`, `None` when empty.
fn rnd_range(rng: &mut impl XofReader, lo: U512, hi: U512) -> Option<U512> {
    if lo >= hi {
        return None;
    }
    Some(lo + rnd_below(rng, hi - lo))
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
    /// (item, T) in emission order.
    items: Vec<(&'static str, usize)>,
    wq: usize,
}

fn ids(regs: &[&[QReg]]) -> Vec<QubitId> {
    regs.iter().flat_map(|r| r.iter().map(|q| QubitId(q.id().into()))).collect()
}

/// Data wires: [r1(257) | r2(257) | ex1(18) | ex2(18) | q(wq) | s_rot(5) | off | gate].
fn build(sched: &StepWidths, wq: usize) -> Harness {
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("r1", RING);
    let r2 = c.alloc_qreg_bits("r2", RING);
    let ex1 = c.alloc_qreg_bits("ex1", 2 * EXP_BITS);
    let ex2 = c.alloc_qreg_bits("ex2", 2 * EXP_BITS);
    let q = c.alloc_qreg_bits("q", wq);
    let s_rot = c.alloc_qreg_bits("srot", SROT);
    let off = c.alloc_qreg("off");
    let gate = c.alloc_qreg("gate");
    let ids = ids(&[&r1, &r2, &ex1, &ex2, &q, &s_rot, std::slice::from_ref(&off), std::slice::from_ref(&gate)]);
    let start = c.b.ops.len();
    let mut marks: Vec<(&'static str, usize)> = Vec::new();
    multiply_forward_marked(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, sched.step, sched, &mut |c, name| {
        marks.push((name, c.b.ops.len()));
    });
    let t = toffoli(&c.b.ops[start..]);
    let scratch = peak_scratch(&c.b.ops[start..], &ids);
    let mut items = Vec::new();
    for w in marks.windows(2) {
        items.push((w[0].0, toffoli(&c.b.ops[w[0].1..w[1].1])));
    }
    Harness { ops: c.b.ops.clone(), ids, t, scratch, items, wq }
}

/// Run up to 64 shots: load the data wires, apply with reset checks, assert
/// phase 0 and every non-data qubit 0, return the data wires per shot.
fn simulate(h: &Harness, shots: &[Vec<bool>], label: &str) -> Vec<Vec<bool>> {
    assert!(!shots.is_empty() && shots.len() <= 64);
    let (nq, nb, _, _) = analyze_ops(h.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-multiply-sim-v1");
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
    mul_rows: usize,
    active: usize,
    filler: usize,
    gate0: usize,
    off_support: usize,
    first_mul: usize,
    first_mul_hi_eb: usize,
    first_mul_lo_eb: usize,
    carry: usize,
    s2_max_model: usize,
    s2_at_bound: usize,
    s2_bound_minus1_carry: usize,
    gap1_zero: usize,
    tight_r2: usize,
    gap2_one: usize,
    gap2_31: usize,
    gap2_max_model: usize,
    zone_edge: usize,
    ring_bottom: usize,
    eb_lo: usize,
    eb_top: usize,
    draining: usize,
    dense: usize,
    b_in_ring: usize,
    synth: usize,
    steps_run: usize,
    shots: usize,
}

/// Is the row inside the step's support (the schedule's guarantees the
/// circuit relies on; module doc of `multiply.rs`)? `Err(reason)` otherwise.
fn support(row: &MulRow, s: &StepWidths, wq: usize) -> Result<(), &'static str> {
    let e_a = bl(&row.a);
    let e_b = bl(&row.b);
    let e_cb = bl(&row.cb);
    let e_ca = bl(&row.ca_old);
    let ca_new = row.ca_new();
    let carry = usize::from(row.carry());
    // M10's windowed compare: cells [cascade_lo, e_cb) of (ca_new >> D) vs cb
    // must decide the full compare (= carry); a tie on the window is the
    // schedule's narrow_lt residue (a carry-row-only miss, <= 2^-33 with the
    // 32-cell-lower cascade bottom, not a circuit defect).
    let lo_c = s.m10_cascade_lo();
    let d = row.s2 + carry;
    let residue_ok = (((ca_new >> d) >> lo_c) < (row.cb >> lo_c)) == (carry == 1);
    let checks: [(bool, &'static str); 19] = [
        (residue_ok, "narrow_lt residue (M10 window tie)"),
        (
            s.v_in_range(e_a) && s.v_in_range(e_b) && s.c_in_range(e_ca) && s.c_in_range(e_cb) && s.c_in_range(bl(&ca_new)),
            "exp_range (an exponent outside the rebase window)",
        ),
        (row.a < row.b, "A >= B"),
        (!row.q.is_zero(), "q = 0"),
        (row.q.trailing_zeros() == row.s2, "s2 != ctz(q)"),
        (e_a <= s.w_a, "e_A > W_A"),
        (e_b >= s.m1_lo_b().max(1), "e_B <= lo_B"),
        (e_b <= s.w_b, "e_B > W_B"),
        (e_cb >= s.lo_cb + 1, "e_cb <= lo_cb"),
        (e_cb <= s.w_c, "e_cb > W_c"),
        (e_ca <= s.w_c, "e_ca > W_c"),
        (bl(&ca_new) <= s.w_c, "bl(ca_new) > W_c"),
        (bl(&ca_new) == e_cb + row.s2 + carry && carry <= 1, "bl(ca_new) theorem"),
        (e_b + bl(&ca_new) <= RING, "e_B + bl(ca_new) > 257"),
        (row.ca_old.is_zero() || row.gap2() < WINDOW, "gap_bound"),
        (row.s2 <= s.s2_bound, "s2 > bound"),
        (row.s2 + carry < (1 << SROT), "s2 + carry overflows the shift word"),
        (bl(&row.q) <= wq, "q wider than the register"),
        (row.ca_old < (row.cb << row.s2), "ca_old >= cb << s2"),
    ];
    for (ok, why) in checks {
        if !ok {
            return Err(why);
        }
    }
    Ok(())
}

fn fits(row: &MulRow, s: &StepWidths, wq: usize) -> bool {
    support(row, s, wq).is_ok()
}

struct Shot {
    data: Vec<bool>,
    expect: Vec<bool>,
}

/// The data wires of a state in the frame of `s` (the exponents rebased:
/// `e - base` mod 2^7, `sched.rs`).
fn state(s: &StepWidths, a: &U512, b: &U512, ca: &U512, cb: &U512, q: &U512, wq: usize, gate: bool) -> Vec<bool> {
    let mut v = ring_lsb(a, cb);
    v.extend(ring_lsb(b, ca));
    v.extend(bits_of(s.reb_v(bl(a)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(cb)), EXP_BITS));
    v.extend(bits_of(s.reb_v(bl(b)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(ca)), EXP_BITS));
    v.extend(bits_of_u(q, wq));
    v.extend(bits_of(0, SROT));
    v.push(false); // off
    v.push(gate);
    v
}

/// An active (or gate = 0) shot of a multiply row; counts its classes.
fn shot(row: &MulRow, s: &StepWidths, wq: usize, gate: bool, cnt: &mut Counts) -> Shot {
    assert!(fits(row, s, wq), "shot: row off the support at step {}", row.step);
    let e_a = bl(&row.a);
    let e_b = bl(&row.b);
    let e_cb = bl(&row.cb);
    let e_ca = bl(&row.ca_old);
    let ca_new = row.ca_new();
    let carry = row.carry();
    let data = state(s, &row.a, &row.b, &row.ca_old, &row.cb, &row.q, wq, gate);
    let expect = if gate {
        let q_new = row.q ^ (one() << row.s2);
        state(s, &row.a, &row.b, &ca_new, &row.cb, &q_new, wq, true)
    } else {
        data.clone()
    };
    cnt.mul_rows += 1;
    cnt.shots += 1;
    if !gate {
        cnt.gate0 += 1;
        return Shot { data, expect };
    }
    cnt.active += 1;
    let synthetic = row.step == SYNTH;
    if synthetic {
        cnt.synth += 1;
    }
    if row.ca_old.is_zero() {
        cnt.first_mul += 1;
        if e_b >= 226 { cnt.first_mul_hi_eb += 1; } else { cnt.first_mul_lo_eb += 1; }
    } else {
        let gap = row.gap2();
        if !synthetic { cnt.gap2_max_model = cnt.gap2_max_model.max(gap); }
        assert!(gap >= 1, "R2 gap 0 before a multiply: step {}", row.step);
        if gap == 1 { cnt.gap2_one += 1; }
        if gap == WINDOW - 1 { cnt.gap2_31 += 1; }
    }
    if carry { cnt.carry += 1; }
    if !synthetic { cnt.s2_max_model = cnt.s2_max_model.max(row.s2); }
    if row.s2 == s.s2_bound { cnt.s2_at_bound += 1; }
    if row.s2 + 1 == s.s2_bound && carry { cnt.s2_bound_minus1_carry += 1; }
    if e_a + e_cb == RING { cnt.gap1_zero += 1; }
    if e_b + row.s2 + e_cb == RING {
        assert!(!carry, "tight row must have carry 0 (fit theorem)");
        cnt.tight_r2 += 1;
    }
    if e_cb == s.lo_cb + 1 { cnt.zone_edge += 1; }
    if e_cb == s.w_c { cnt.ring_bottom += 1; }
    if e_b == s.lo_b + 1 { cnt.eb_lo += 1; }
    if e_b == s.w_b { cnt.eb_top += 1; }
    if row.a.is_zero() { cnt.draining += 1; }
    if row.dense { cnt.dense += 1; }
    if e_b > RING - 1 - s.w_c { cnt.b_in_ring += 1; }
    let _ = e_ca;
    Shot { data, expect }
}

/// Filler shot (gate = 0) from any row's pre-step state.
fn filler(s: &StepWidths, pre: &Pre, wq: usize, cnt: &mut Counts) -> Shot {
    let data = state(s, &pre.a, &pre.b, &pre.ca, &pre.cb, &pre.q, wq, false);
    cnt.filler += 1;
    cnt.shots += 1;
    Shot { data: data.clone(), expect: data }
}

/// Forward on `shots`, check every data wire against `expect`.
fn run_batch(h: &Harness, shots: &[Shot], label: &str) {
    let data: Vec<Vec<bool>> = shots.iter().map(|s| s.data.clone()).collect();
    let out = simulate(h, &data, label);
    for (i, (o, s)) in out.iter().zip(shots).enumerate() {
        if o != &s.expect {
            let names = ["r1", "r2", "ex1", "ex2", "q", "srot", "off", "gate"];
            let widths = [RING, RING, 2 * EXP_BITS, 2 * EXP_BITS, h.wq, SROT, 1, 1];
            let mut at = 0;
            let mut diff = String::new();
            for (n, w) in names.iter().zip(widths) {
                let got: Vec<usize> = (0..w).filter(|&k| o[at + k] != s.expect[at + k]).collect();
                if !got.is_empty() {
                    diff.push_str(&format!(" {n}@{got:?}"));
                }
                at += w;
            }
            panic!("{label}: shot {i} differs:{diff}");
        }
    }
}

/// Synthetic multiply row in the model's own terms (module doc). `hi_lo`
/// selects `ca_old >> s2` in `[max(lo, carry ? 2^e_cb - cb : 0), cb)` with the
/// requested bit-length when `gap` is given (`gap = 257 - e_B - bl(ca_old)`).
struct Spec {
    e_b: usize,
    e_cb: usize,
    s2: usize,
    carry: bool,
    ca_zero: bool,
    gap: Option<usize>,
    e_a: Option<usize>,
    dense: bool,
    b_kind: u8, // 0 random, 1 all ones, 2 = 2^(e_B - 1)
}

#[allow(clippy::too_many_arguments)]
fn synth(rng: &mut impl XofReader, s: &StepWidths, wq: usize, spec: &Spec) -> Option<MulRow> {
    let Spec { e_b, e_cb, s2, carry, ca_zero, gap, e_a, dense, b_kind } = *spec;
    if e_b == 0 || e_cb == 0 || wq < s2 + 1 {
        return None;
    }
    let b = match b_kind {
        0 => rnd_bl(rng, e_b, dense),
        1 => pow2(e_b) - one(),
        _ => pow2(e_b - 1),
    };
    let mut cb = rnd_bl(rng, e_cb, dense);
    if carry && cb == pow2(e_cb - 1) {
        if e_cb == 1 {
            return None;
        }
        cb += one();
    }
    let ca_old = if ca_zero {
        if carry {
            return None;
        }
        U512::ZERO
    } else {
        let lo_hi = if carry { pow2(e_cb) - cb } else { U512::ZERO };
        let hi = match gap {
            Some(g) => {
                let bl_ca = RING.checked_sub(e_b + g)?;
                let hb = bl_ca.checked_sub(s2)?;
                if hb == 0 {
                    return None;
                }
                rnd_range(rng, lo_hi.max(pow2(hb - 1)), cb.min(pow2(hb)))?
            }
            None => rnd_range(rng, lo_hi, cb)?,
        };
        let low = if s2 == 0 { U512::ZERO } else if dense { pow2(s2) - one() } else { rnd_below(rng, pow2(s2)) };
        (hi << s2) + low
    };
    let e_a = e_a.unwrap_or_else(|| {
        let mut bytes = [0u8; 2];
        rng.read(&mut bytes);
        let top = e_b.min(s.w_a).min(RING - e_cb);
        (u16::from_le_bytes(bytes) as usize) % (top + 1)
    });
    let a = if e_a == 0 {
        U512::ZERO
    } else if e_a < e_b {
        rnd_bl(rng, e_a, dense)
    } else {
        // e_a == e_b: below B
        rnd_range(rng, pow2(e_a - 1), b)?
    };
    let q = {
        let room = wq - s2 - 1;
        let r = if room == 0 { U512::ZERO } else { rnd_below(rng, pow2(room)) };
        (r << (s2 + 1)) | (one() << s2)
    };
    let row = MulRow { step: SYNTH, a, b, ca_old, cb, q, s2, dense };
    if !fits(&row, s, wq) || row.carry() != carry {
        return None;
    }
    Some(row)
}

fn random_inputs() -> Vec<U512> {
    let mut seed = Shake256::default();
    seed.update(b"packed-multiply-inputs-v1");
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

/// q width for a step: the schedule's envelope, or wider if a shot needs it.
fn q_width(s: &StepWidths, rows: &[&MulRow], fill: &[&Pre]) -> usize {
    let need = rows.iter().map(|r| bl(&r.q)).chain(fill.iter().map(|p| bl(&p.q))).max().unwrap_or(0);
    s.w_q.max(need).max(1)
}

struct EnvGuard {
    saved: Vec<(&'static str, Option<String>)>,
}

impl EnvGuard {
    fn set(vars: &[(&'static str, Option<&str>)]) -> Self {
        let saved = vars
            .iter()
            .map(|(k, v)| {
                let old = std::env::var(k).ok();
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
        for (k, v) in self.saved.drain(..) {
            match v {
                Some(v) => std::env::set_var(k, v),
                None => std::env::remove_var(k),
            }
        }
    }
}

/// Synthetic specs for a step: the required classes (module doc). `e_B` is
/// placed so that the row is on the support: with `ca_old != 0` the R2 gap
/// bound needs `226 <= e_B + e_cb + s2` and the pair bound `e_B + e_cb + s2 +
/// carry <= 257`; a gap-targeted row has `bl(ca_old) = e_cb + s2 - [!carry]`
/// (a carry needs `ca_old >> s2 >= 2^e_cb - cb > 2^(e_cb-1)`, i.e. the full
/// `e_cb + s2` bits). The R2 gap before a multiply is never 0: `bl(ca_new) >=
/// bl(ca_old) + 1` always (`ca_old < cb << s2 <= ca_new`, and a full-length
/// `ca_old >> s2` forces the carry), so `e_B + bl(ca_new) <= 257` gives
/// `gap >= 1`; the minimum class is gap 1.
fn specs_for(s: &StepWidths, wq: usize) -> Vec<(&'static str, Spec)> {
    let s2b = s.s2_bound.min((1 << SROT) - 1).min(wq.saturating_sub(1));
    let mid_cb = (s.lo_cb + 1 + s.w_c) / 2;
    let clamp_b = |e: i64| -> usize { e.clamp((s.lo_b + 1) as i64, s.w_b as i64) as usize };
    let clamp_cb = |e: i64| -> usize { e.clamp((s.lo_cb + 1) as i64, s.w_c as i64) as usize };
    // e_cb for a row whose bl(ca_new) = e_cb + s2 + carry must fit W_c, 2 below
    let cb_for = |s2: usize, carry: bool| -> usize { clamp_cb(s.w_c as i64 - s2 as i64 - i64::from(carry) - 2) };
    let eb_for = |e_cb: usize, s2: usize, carry: bool| -> usize {
        clamp_b(RING as i64 - e_cb as i64 - s2 as i64 - i64::from(carry) - 8)
    };
    let eb_gap = |e_cb: usize, s2: usize, carry: bool, g: usize| -> usize {
        clamp_b(RING as i64 - g as i64 - (e_cb + s2) as i64 + i64::from(!carry))
    };
    let base = |e_b: usize, e_cb: usize, s2: usize, carry: bool| Spec {
        e_b, e_cb, s2, carry, ca_zero: false, gap: None, e_a: None, dense: false, b_kind: 0,
    };
    let mut v: Vec<(&'static str, Spec)> = Vec::new();
    // maximal s2 (carry 0) and s2 = bound - 1 with carry (D = bound); e_cb so
    // that bl(ca_new) fits W_c
    {
        let e_cb = cb_for(s2b, false);
        v.push(("s2_max", base(eb_for(e_cb, s2b, false), e_cb, s2b, false)));
        if s2b >= 1 {
            let e_cb = cb_for(s2b - 1, true);
            v.push(("s2_max-1_carry", base(eb_for(e_cb, s2b - 1, true), e_cb, s2b - 1, true)));
        }
    }
    // carry and no carry at a middle shift
    v.push(("carry", base(eb_for(mid_cb, s2b / 2, true), mid_cb, s2b / 2, true)));
    v.push(("nocarry", base(eb_for(mid_cb, s2b / 2, false), mid_cb, s2b / 2, false)));
    // zone edge e_cb = lo_cb + 1, both carries
    let edge = s.lo_cb + 1;
    v.push(("zone_edge", base(eb_for(edge, s2b / 3, false), edge, s2b / 3, false)));
    v.push(("zone_edge_carry", base(eb_for(edge, s2b / 3, true), edge, s2b / 3, true)));
    // ring bottom: e_cb = W_c (s2 = carry = 0), and bl(ca_new) = W_c with a carry
    v.push(("ring_bottom", base(eb_for(s.w_c, 0, false), s.w_c, 0, false)));
    if s.w_c >= s2b / 2 + 2 {
        let e_cb = s.w_c - s2b / 2 - 1;
        v.push(("ring_full_carry", base(eb_for(e_cb, s2b / 2, true), e_cb, s2b / 2, true)));
    }
    // tight R2: e_B + s2 + e_cb = 257 (carry 0); B all ones (the absorb wire holds B's MSB = 1)
    if RING > mid_cb + s2b / 2 {
        let e_b = RING - mid_cb - s2b / 2;
        v.push(("tight_r2", Spec { b_kind: 1, ..base(e_b, mid_cb, s2b / 2, false) }));
        v.push(("tight_r2_rnd", base(e_b, mid_cb, s2b / 2, false)));
    }
    // R1 gap 0: A's MSB one wire below cb's MSB. The pair bound forces
    // e_B = e_A (A < B of the same length), s2 = 0 and carry = 0.
    {
        let e_a = eb_for(mid_cb, 0, false).max(1);
        let e_cb = RING - e_a;
        v.push(("gap1_zero", Spec { e_a: Some(e_a), ..base(e_a, e_cb, 0, false) }));
        v.push(("gap1_zero_ca0", Spec { e_a: Some(e_a), ca_zero: true, dense: true, ..base(e_a, e_cb, 0, false) }));
    }
    // R2 gap 1 (the minimum: bl(ca_new) >= bl(ca_old) + 1 always) / 25 / 31 before the multiply
    v.push(("gap2_one", Spec { gap: Some(1), ..base(eb_gap(mid_cb, s2b / 4, false, 1), mid_cb, s2b / 4, false) }));
    v.push(("gap2_one_carry", Spec { gap: Some(1), ..base(eb_gap(mid_cb, s2b / 4, true, 1), mid_cb, s2b / 4, true) }));
    v.push(("gap2_31", Spec { gap: Some(WINDOW - 1), ..base(eb_gap(mid_cb, s2b / 4, false, WINDOW - 1), mid_cb, s2b / 4, false) }));
    v.push(("gap2_31_carry", Spec { gap: Some(WINDOW - 1), ..base(eb_gap(mid_cb, s2b / 4, true, WINDOW - 1), mid_cb, s2b / 4, true) }));
    v.push(("gap2_25_carry", Spec { gap: Some(25), ..base(eb_gap(mid_cb, s2b / 4, true, 25), mid_cb, s2b / 4, true) }));
    // first multiplies: ca_old = 0 with e_B >= 226 (wrap) and <= 225 (sentinel)
    let hi_eb = if s.w_b >= 226 { (226 + s.w_b) / 2 } else { RING };
    v.push(("ca0_hi_eb", Spec { ca_zero: true, ..base(hi_eb, mid_cb, s2b / 2, false) }));
    v.push(("ca0_hi_eb_ones", Spec { ca_zero: true, b_kind: 1, ..base(hi_eb, mid_cb, 0, false) }));
    v.push(("ca0_lo_eb", Spec { ca_zero: true, ..base(clamp_b(225.min(eb_for(mid_cb, s2b / 2, false) as i64)), mid_cb, s2b / 2, false) }));
    // e_B at the schedule edges (M1 rotation 1 and max)
    v.push(("eb_lo", base(s.lo_b + 1, mid_cb, s2b / 2, false)));
    v.push(("eb_lo_ca0", Spec { ca_zero: true, ..base(s.lo_b + 1, mid_cb, s2b / 2, false) }));
    {
        // e_B = W_B needs e_cb + s2 + carry <= 257 - W_B
        let e_cb = clamp_cb(RING as i64 - s.w_b as i64 - 1 - 3);
        v.push(("eb_top", base(s.w_b, e_cb, 2, true)));
        v.push(("eb_top_nocarry", base(s.w_b, e_cb, 2, false)));
        v.push(("eb_top_ca0", Spec { ca_zero: true, ..base(s.w_b, e_cb, 2, false) }));
    }
    // draining: A = 0, B = 1
    v.push(("draining", Spec { e_a: Some(0), ..base(1, mid_cb, s2b / 2, false) }));
    v.push(("draining_carry", Spec { e_a: Some(0), ..base(1, mid_cb, s2b / 2, true) }));
    // draining with ca_new filling the ring: e_B = 1, gap 3, carry (bl(ca_old) = e_cb + s2 = 253)
    if RING - 1 - 3 >= s2b / 2 {
        v.push(("draining_full", Spec { e_a: Some(0), gap: Some(3), ..base(1, RING - 1 - 3 - s2b / 2, s2b / 2, true) }));
    }
    // dense everything (all-ones cb forces the carry whenever ca_old >> s2 != 0;
    // the no-carry dense rows are first multiplies)
    v.push(("dense_ca0", Spec { dense: true, ca_zero: true, ..base(eb_for(mid_cb, s2b / 2, false), mid_cb, s2b / 2, false) }));
    v.push(("dense_carry", Spec { dense: true, ..base(eb_for(mid_cb, s2b / 2, true), mid_cb, s2b / 2, true) }));
    {
        let e_cb = cb_for(s2b, false);
        v.push(("dense_s2max_ca0", Spec { dense: true, ca_zero: true, ..base(eb_for(e_cb, s2b, false), e_cb, s2b, false) }));
        if s2b >= 1 {
            let e_cb = cb_for(s2b - 1, true);
            v.push(("dense_s2max-1_carry", Spec { dense: true, ..base(eb_for(e_cb, s2b - 1, true), e_cb, s2b - 1, true) }));
        }
    }
    v
}

pub(super) fn run() {
    let _env = EnvGuard::set(&[
        ("MIDQ_KG_ZERO_LAYER", Some("1")),
        ("MIDQ_CHUNKED_PREFIX", None),
        ("MIDQ_PACKED_CTZ_ROOM", Some("12")),
    ]);
    let inputs = random_inputs();
    let traces: Vec<Trace> = inputs.iter().map(|&x| trace(x)).collect();
    let mut cnt = Counts::default();
    let mut seed = Shake256::default();
    seed.update(b"packed-multiply-synth-v1");
    let mut rng = seed.finalize_xof();
    let mut t_rows: Vec<String> = Vec::new();
    let report_steps = [100usize, 250, 378];

    // ---- every step with a multiply row among the inputs --------------------
    for step in 0..NSTEPS {
        let sched = StepWidths::from_schedule(step);
        let rows: Vec<&MulRow> = traces.iter().filter_map(|t| t.mul[step].as_ref()).collect();
        if rows.is_empty() {
            continue;
        }
        let fill: Vec<&Pre> = traces.iter().map(|t| &t.pre[step]).collect();
        let wq = q_width(&sched, &rows, &fill);
        let h = build(&sched, wq);
        let mut shots: Vec<Shot> = Vec::new();
        let mut shots0: Vec<Shot> = Vec::new();
        for t in &traces {
            match &t.mul[step] {
                Some(row) if fits(row, &sched, wq) => {
                    shots.push(shot(row, &sched, wq, true, &mut cnt));
                    shots0.push(shot(row, &sched, wq, false, &mut cnt));
                }
                Some(row) => {
                    cnt.off_support += 1;
                    eprintln!(
                        "PACKED_MULTIPLY off-support model row at step {step}: {} (e_A {} e_B {} e_ca {} e_cb {} s2 {})",
                        support(row, &sched, wq).err().unwrap_or("?"), bl(&row.a), bl(&row.b), bl(&row.ca_old), bl(&row.cb), row.s2
                    );
                    shots.push(filler(&sched, &t.pre[step], wq, &mut cnt));
                }
                None => shots.push(filler(&sched, &t.pre[step], wq, &mut cnt)),
            }
        }
        run_batch(&h, &shots, &format!("mul-s{step}"));
        if !shots0.is_empty() {
            run_batch(&h, &shots0, &format!("mul0-s{step}"));
        }
        cnt.steps_run += 1;
        if report_steps.contains(&step) || step == 1 || step == 480 || step == 529 {
            let items: Vec<String> = h.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
            t_rows.push(format!(
                "PACKED_MULTIPLY T step {step:3} W_A {:3} W_B {:3} W_c {:3} wq {:2} lo_B {:3} lo_cb {:3} zone_start {:3} rb {}/{}: T {:5} scratch_peak {:2} | {}",
                sched.w_a, sched.w_b, sched.w_c, wq, sched.lo_b, sched.lo_cb, sched.mul_zone_start(),
                sched.rb_mul.min(SROT), sched.rb_mul_plus_carry().min(SROT), h.t, h.scratch, items.join(", ")
            ));
        }
    }

    // ---- T per traversal: every step's multiply at the static envelope (count only) ----
    {
        let mut sum = 0usize;
        let mut max_t = (0usize, 0usize);
        let mut max_scratch = 0usize;
        for step in 0..NSTEPS {
            let sched = StepWidths::from_schedule(step);
            let h = build(&sched, sched.w_q.max(1));
            sum += h.t;
            if h.t > max_t.0 { max_t = (h.t, step); }
            max_scratch = max_scratch.max(h.scratch);
        }
        t_rows.push(format!(
            "PACKED_MULTIPLY T: sum over {NSTEPS} steps (static schedule, one direction) {sum} (per step avg {}), max {} at step {}, max scratch {max_scratch}",
            sum / NSTEPS, max_t.0, max_t.1
        ));
    }

    // ---- T at the design's own envelopes (packed_design_steps.csv rows; count only) ----
    for (step, w_a, w_c, lo_a, lo_c, wq, model) in [
        (100usize, 215usize, 85usize, 137usize, 7usize, 22usize, 4228usize),
        (250, 144, 184, 66, 106, 24, 5840),
        (378, 76, 256, 0, 178, 28, 6856),
    ] {
        let sched = StepWidths::new(step, w_a, w_a, w_c, wq, lo_a, lo_a, lo_c, lo_c, 31, 31);
        let h = build(&sched, wq);
        let items: Vec<String> = h.items.iter().map(|(n, t)| format!("{n} {t}")).collect();
        t_rows.push(format!(
            "PACKED_MULTIPLY T design-envelope step {step:3} W_A {w_a:3} W_c {w_c:3} lo_A {lo_a:3} lo_c {lo_c:3} wq {wq:2} zone_start {:3}: T {:5} (model {model}, refuter deltas +37) scratch_peak {:2} | {}",
            sched.mul_zone_start(), h.t, h.scratch, items.join(", ")
        ));
    }

    // ---- synthetic rows at chosen steps --------------------------------------
    for &step in &[1usize, 5, 30, 100, 200, 250, 300, 378, 440, 480, 500, 520, 529] {
        let sched = StepWidths::from_schedule(step);
        let wq = sched.w_q.max(1);
        let h = build(&sched, wq);
        let mut made: Vec<&str> = Vec::new();
        let mut missing: Vec<&str> = Vec::new();
        for (name, spec) in specs_for(&sched, wq) {
            let mut got = None;
            for _ in 0..16 {
                if let Some(r) = synth(&mut rng, &sched, wq, &spec) {
                    got = Some(r);
                    break;
                }
            }
            if let Some(row) = got {
                let label = format!(
                    "synth-s{step}-{name} (e_A {} e_B {} e_ca {} e_cb {} s2 {} carry {})",
                    bl(&row.a), bl(&row.b), bl(&row.ca_old), bl(&row.cb), row.s2, u8::from(row.carry())
                );
                let s1 = shot(&row, &sched, wq, true, &mut cnt);
                let s0 = shot(&row, &sched, wq, false, &mut cnt);
                run_batch(&h, &[s1, s0], &label);
                made.push(name);
            } else {
                missing.push(name);
            }
        }
        assert!(!made.is_empty(), "no synthetic row realisable at step {step}");
        eprintln!("PACKED_MULTIPLY synth step {step}: {} rows [{}]; unrealisable [{}]", made.len(), made.join(" "), missing.join(" "));
    }

    for r in &t_rows {
        eprintln!("{r}");
    }
    eprintln!(
        "PACKED_MULTIPLY classes: steps {} shots {} active {} filler {} gate0 {} off_support {} first_mul {} (e_B>=226: {}, <=225: {}) carry {} \
         s2_max_model {} s2_at_bound {} s2_bound-1_carry {} gap1_zero {} tight_r2 {} gap2_one {} gap2_31 {} gap2_max_model {} zone_edge {} ring_bottom {} \
         eb_lo {} eb_top {} draining {} dense {} b_in_ring {} synth {}",
        cnt.steps_run, cnt.shots, cnt.active, cnt.filler, cnt.gate0, cnt.off_support, cnt.first_mul, cnt.first_mul_hi_eb, cnt.first_mul_lo_eb,
        cnt.carry, cnt.s2_max_model, cnt.s2_at_bound, cnt.s2_bound_minus1_carry, cnt.gap1_zero, cnt.tight_r2, cnt.gap2_one, cnt.gap2_31,
        cnt.gap2_max_model, cnt.zone_edge, cnt.ring_bottom, cnt.eb_lo, cnt.eb_top, cnt.draining, cnt.dense, cnt.b_in_ring, cnt.synth
    );
    assert!(cnt.active >= NINPUTS * 100, "too few active rows: {}", cnt.active);
    assert!(cnt.off_support * 50 <= cnt.active, "too many model rows outside the static schedule's support: {}", cnt.off_support);
    for (name, v) in [
        ("first_mul_hi_eb", cnt.first_mul_hi_eb),
        ("first_mul_lo_eb", cnt.first_mul_lo_eb),
        ("carry", cnt.carry),
        ("s2_at_bound", cnt.s2_at_bound),
        ("s2_bound_minus1_carry", cnt.s2_bound_minus1_carry),
        ("gap1_zero", cnt.gap1_zero),
        ("tight_r2", cnt.tight_r2),
        ("gap2_one", cnt.gap2_one),
        ("gap2_31", cnt.gap2_31),
        ("zone_edge", cnt.zone_edge),
        ("ring_bottom", cnt.ring_bottom),
        ("eb_lo", cnt.eb_lo),
        ("eb_top", cnt.eb_top),
        ("draining", cnt.draining),
        ("dense", cnt.dense),
        ("b_in_ring", cnt.b_in_ring),
        ("gate0", cnt.gate0),
    ] {
        assert!(v > 0, "required class {name} is empty");
    }
    eprintln!(
        "PACKED_MULTIPLY PASS: {} active multiply rows ({} model, {} synthetic) + {} gate=0 rows + {} filler rows over {} steps; value, phase, ancillae",
        cnt.active, cnt.active - cnt.synth, cnt.synth, cnt.gate0, cnt.filler, cnt.steps_run
    );
}
