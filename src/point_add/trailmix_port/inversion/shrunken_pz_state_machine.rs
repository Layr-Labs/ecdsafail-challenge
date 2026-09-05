//! Reversible unpacked PZ inversion as a bit-by-bit pipelined state machine
//! (design reference: `scripts/kaliski_test.py` `pz_big_step`). This supersedes
//! the full-division `shrunken_pz_primitives` module, whose coarser granularity
//! needed a fat quotient pad and did not handle large termination quotients.
//!
//! Per iteration (fixed count ~= sum of quotient bitlengths), gated on the state
//! flags so termination is intrinsic (no separate counter):
//!   DIVISION substep:  s = bitlen(A)-bitlen(B); align B<<s; if A>=B { A-=B;
//!                      `q_div` ^= 1<<s }; restore B>>s. A<B => `div_active=0`.
//!   MULTIPLY substep (pipelined): s = `ctz(q_mul)`; clear it; a += b<<s; restore.
//!                      `q_mul==0` => swap a,b; flip parity; `mul_active=0`.
//!   TRANSITION: q_div->q_mul; swap A,B; divide builds the NEXT quotient while
//!               the multiply drains the PREVIOUS. q pads are TINY (one quotient).
//! All shifts are `controlled_cyclic_rotate` (rotate-in-place, fixed width).
//! Up front: normalize x -> min(x, P-x) (sgn); final a corrected by parity ^ sgn.

#![allow(dead_code)]

use std::cell::RefCell;

#[path = "chunked_bitlength.rs"]
pub(crate) mod chunked_bitlength;

#[path = "quotient_code.rs"]
mod quotient_code;
pub(crate) use quotient_code::selftest::run as midq_quotient_code_selftest;

#[path = "counter_tape.rs"]
pub(crate) mod counter_tape;

#[path = "retained_division.rs"]
mod retained_division;
use retained_division::division_substep_retained_lengths;
pub(crate) use retained_division::tests::retained_lengths_match_original;

use crate::circuit::{OperationType, QubitId};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{
    borrow_compare_refs, clear_borrow_compare_refs,
};

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(default)
}

fn trailmix_srot_width() -> usize {
    // The generated schedule's shift bounds need six bits on valid samples.
    // Keep an env override for experiments.
    env_usize("TRAILMIX_SROT_W", 6).max(1)
}

fn trailmix_counter_width() -> usize {
    if std::env::var("TRAILMIX_NO_COUNTER").ok().as_deref() == Some("1") {
        0
    } else {
        env_usize("TRAILMIX_COUNTER_W", 10)
    }
}

fn lowq_one_a_elim_enabled() -> bool {
    if std::env::var("LOWQ_ONE_A_ELIM").ok().as_deref() != Some("1") {
        return false;
    }
    let target = env_usize("TRAILMIX_Q_TARGET", 0);
    assert!(
        matches!(target, 683 | 684 | 685),
        "LOWQ_ONE_A_ELIM is sealed to TRAILMIX_Q_TARGET=683/684/685"
    );
    true
}

fn lowq_borrow_passenger_carry_enabled() -> bool {
    if std::env::var("LOWQ_BORROW_PASSENGER_CARRY")
        .ok()
        .as_deref()
        != Some("1")
    {
        return false;
    }
    assert!(
        lowq_one_a_elim_enabled(),
        "LOWQ_BORROW_PASSENGER_CARRY requires LOWQ_ONE_A_ELIM=1"
    );
    assert_eq!(
        std::env::var("LOWQ_CLZ_DIFF_CONST_FOLD").ok().as_deref(),
        Some("1"),
        "LOWQ_BORROW_PASSENGER_CARRY requires LOWQ_CLZ_DIFF_CONST_FOLD=1"
    );
    true
}

fn lowq_inline_active_enabled() -> bool {
    std::env::var("LOWQ_INLINE_ACTIVE").ok().as_deref() == Some("1")
}

fn lowq_delay_gate_hold_enabled() -> bool {
    std::env::var("LOWQ_DELAY_GATE_HOLD").ok().as_deref() == Some("1")
}

fn lowq_hybrid_gate_hold_enabled() -> bool {
    std::env::var("LOWQ_HYBRID_GATE_HOLD").ok().as_deref() == Some("1")
}

fn lowq_hybrid_cache_ctz_enabled() -> bool {
    std::env::var("LOWQ_HYBRID_CACHE_CTZ").ok().as_deref() == Some("1")
}

fn lowq_hybrid_inplace_ctz_enabled() -> bool {
    std::env::var("LOWQ_HYBRID_INPLACE_CTZ").ok().as_deref() == Some("1")
}

fn lowq_compact_kganc_enabled() -> bool {
    std::env::var("LOWQ_COMPACT_KGANC").ok().as_deref() == Some("1")
}

fn lowq_recompute_gate_predicate_enabled() -> bool {
    std::env::var("LOWQ_RECOMPUTE_GATE_PREDICATE")
        .ok()
        .as_deref()
        == Some("1")
}

fn trailmix_q_width(wq: usize) -> usize {
    let w = wq.max(1);
    std::env::var("TRAILMIX_Q_CAP")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .map_or(w, |cap| w.min(cap.max(1)))
}

/// Per-step quotient width with SELECTIVE peak-targeting.
///
/// The global qubit peak at a `shrunken_pz` step is
///   2*max(wa,wb) + 2*max(wca,wcb) + q_width + FIXED.
/// A blunt global `TRAILMIX_Q_CAP` clamps q on ALL ~490 steps (most have
/// universal q in 23..38), but only the peak-binding step(s) need a smaller q
/// to lower the global peak. Clamping the rest just manufactures classical
/// misses (overflowed quotients) without helping the peak.
///
/// `TRAILMIX_Q_TARGET=T` instead gives each step a budget so that its working
/// width never exceeds T: `q <= T - 2*max(wa,wb) - 2*max(wca,wcb)`. Steps whose
/// other registers are small keep their full natural q (no miss); only the
/// wide-carry peak step(s) get q trimmed, and only by the minimum needed.
/// Falls back to `trailmix_q_width` (global cap) when `TRAILMIX_Q_TARGET` unset.
/// Cap the shared A/B register width (both A and B are resized to max(wa,wb)).
/// `TRAILMIX_AB_CAP` trims it on the steps where it would otherwise bind the peak.
fn trailmix_ab_width(wab: usize) -> usize {
    let w = wab.max(1);
    std::env::var("TRAILMIX_AB_CAP")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .map_or(w, |c| w.min(c.max(1)))
}

/// Cap the shared ca/cb cofactor register width (both resized to max(wca,wcb)).
/// `TRAILMIX_CACB_CAP` trims the dominant 2*245 carry pair at the peak step.
fn trailmix_cacb_width(wcacb: usize) -> usize {
    let w = wcacb.max(1);
    std::env::var("TRAILMIX_CACB_CAP")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .map_or(w, |c| w.min(c.max(1)))
}

fn trailmix_q_width_step(wq: usize, wa: usize, wb: usize, wca: usize, wcb: usize) -> usize {
    let natural = wq.max(1);
    let target = std::env::var("TRAILMIX_Q_TARGET")
        .ok()
        .and_then(|s| s.parse::<usize>().ok());
    let Some(target) = target else {
        return trailmix_q_width(wq);
    };
    // q budget is computed from the (possibly capped) A/B and ca/cb widths so the
    // working width 2*ab + 2*cacb + q meets `target` consistently with the resizes.
    let other = 2 * trailmix_ab_width(wa.max(wb)) + 2 * trailmix_cacb_width(wca.max(wcb));
    let budget = target.saturating_sub(other).max(1);
    // Still honor a global Q_CAP if both are set (take the tighter bound).
    let capped = natural.min(budget);
    std::env::var("TRAILMIX_Q_CAP")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .map_or(capped, |cap| capped.min(cap.max(1)))
        .max(1)
}

fn compute_active(c: &mut Circuit, counter: &[QReg]) -> QReg {
    let active = c.alloc_qreg("active");
    if counter.is_empty() {
        c.x(&active);
    } else {
        or_is_zero(c, counter, &active);
    }
    active
}

fn uncompute_active(c: &mut Circuit, counter: &[QReg], active: &QReg) {
    if counter.is_empty() {
        c.x(active);
    } else {
        clear_zero_predicate(c, counter, active, false);
    }
}

fn xor_counter_zero_and_gate(c: &mut Circuit, counter: &[QReg], gate: &QReg, out: &QReg) {
    use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
    if counter.is_empty() {
        c.cx(gate, out);
        return;
    }
    let prev = c.push_section("p.orz");
    for q in counter {
        c.x(q);
    }
    let mut refs: Vec<&QReg> = Vec::with_capacity(counter.len() + 1);
    refs.push(gate);
    refs.extend(counter.iter());
    mcx_clean_k(c, &refs, out);
    for q in counter {
        c.x(q);
    }
    c.pop_section(&prev);
}

#[derive(Clone, Copy)]
pub(crate) enum GateControl<'a> {
    Direct(&'a QReg),
    DelayedAnd { active: &'a QReg, gate: &'a QReg },
    Hybrid(&'a HybridGateControl<'a>),
    RecomputeLt {
        x: &'a [QReg],
        y: &'a [QReg],
        active: &'a QReg,
    },
}

pub(crate) struct HybridGateControl<'a> {
    active: &'a QReg,
    gate: &'a QReg,
    held: RefCell<Option<QReg>>,
}

impl<'a> HybridGateControl<'a> {
    fn new(active: &'a QReg, gate: &'a QReg) -> Self {
        Self {
            active,
            gate,
            held: RefCell::new(None),
        }
    }

    fn materialize(&self, c: &mut Circuit) {
        if self.held.borrow().is_some() {
            return;
        }
        let g = c.alloc_qreg("gh.g");
        c.ccx(self.active, self.gate, &g);
        *self.held.borrow_mut() = Some(g);
    }

    fn release(&self, c: &mut Circuit) {
        if let Some(g) = self.held.borrow_mut().take() {
            clear_hybrid_and(c, self.active, self.gate, &g);
            c.zero_and_free(g);
        }
    }

    fn with(&self, c: &mut Circuit, body: impl FnOnce(&mut Circuit, &QReg)) {
        self.materialize(c);
        let held = self.held.borrow();
        body(c, held.as_ref().expect("hybrid gate was materialized"));
    }

    fn with_ephemeral(&self, c: &mut Circuit, body: impl FnOnce(&mut Circuit, &QReg)) {
        self.release(c);
        let g = c.alloc_qreg("gh.g");
        c.ccx(self.active, self.gate, &g);
        body(c, &g);
        clear_hybrid_and(c, self.active, self.gate, &g);
        c.zero_and_free(g);
    }
}

// Both controls must retain their materialization-time values, the same
// precondition required by the former coherent CCX cleanup.
fn clear_hybrid_and(c: &mut Circuit, active: &QReg, gate: &QReg, out: &QReg) {
    if std::env::var("MIDQ_MEASURE_GATE_AND").ok().as_deref() == Some("1") {
        c.clear_and(out, active, gate);
    } else {
        c.ccx(active, gate, out);
    }
}

fn with_gate_control(c: &mut Circuit, control: GateControl<'_>, body: impl FnOnce(&mut Circuit, &QReg)) {
    match control {
        GateControl::Direct(g) => body(c, g),
        GateControl::DelayedAnd { active, gate } => {
            let g = c.alloc_qreg("gh.g");
            c.ccx(active, gate, &g);
            body(c, &g);
            c.ccx(active, gate, &g);
            c.zero_and_free(g);
        }
        GateControl::Hybrid(control) => control.with(c, body),
        GateControl::RecomputeLt { x, y, active } => {
            let lt = c.alloc_qreg("gh.lt");
            let xr: Vec<&QReg> = x.iter().collect();
            let yr: Vec<&QReg> = y.iter().collect();
            borrow_compare_refs(c, &xr, &yr, &lt);
            let g = c.alloc_qreg("gh.g");
            c.ccx(active, &lt, &g);
            body(c, &g);
            c.ccx(active, &lt, &g);
            c.zero_and_free(g);
            borrow_compare_refs(c, &xr, &yr, &lt);
            c.zero_and_free(lt);
        }
    }
}

fn with_peak_gate_control(
    c: &mut Circuit,
    control: GateControl<'_>,
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    match control {
        GateControl::Direct(g) => body(c, g),
        GateControl::DelayedAnd { active, gate } => {
            let g = c.alloc_qreg("gh.g");
            c.ccx(active, gate, &g);
            body(c, &g);
            c.ccx(active, gate, &g);
            c.zero_and_free(g);
        }
        GateControl::Hybrid(control) => control.with_ephemeral(c, body),
        GateControl::RecomputeLt { x, y, active } => {
            let lt = c.alloc_qreg("gh.lt");
            let xr: Vec<&QReg> = x.iter().collect();
            let yr: Vec<&QReg> = y.iter().collect();
            borrow_compare_refs(c, &xr, &yr, &lt);
            let g = c.alloc_qreg("gh.g");
            c.ccx(active, &lt, &g);
            body(c, &g);
            c.ccx(active, &lt, &g);
            c.zero_and_free(g);
            borrow_compare_refs(c, &xr, &yr, &lt);
            c.zero_and_free(lt);
        }
    }
}

fn without_gate_control(c: &mut Circuit, control: GateControl<'_>, body: impl FnOnce(&mut Circuit)) {
    if let GateControl::Hybrid(control) = control {
        control.release(c);
    }
    body(c);
}

fn cache_ctz_control(control: GateControl<'_>) -> bool {
    matches!(
        control,
        GateControl::Hybrid(_) | GateControl::RecomputeLt { .. }
    ) && lowq_hybrid_cache_ctz_enabled()
}

fn bit_length_ctz(
    c: &mut Circuit,
    control: GateControl<'_>,
    src: &[&QReg],
    s: &[QReg],
    dec: bool,
    borrowed_carry: Option<&QReg>,
) {
    if cache_ctz_control(control) && lowq_hybrid_inplace_ctz_enabled() {
        bit_length_ctz_inplace(c, src, s, dec);
    } else if cache_ctz_control(control) {
        bit_length_lean(c, src, s, dec, borrowed_carry);
    } else {
        without_gate_control(c, control, |c| {
            bit_length_lean(c, src, s, dec, borrowed_carry);
        });
    }
}

fn with_ctz_gate_control(
    c: &mut Circuit,
    control: GateControl<'_>,
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    if cache_ctz_control(control) {
        with_gate_control(c, control, body);
    } else {
        with_peak_gate_control(c, control, body);
    }
}

fn bit_length_ctz_inplace(
    circ: &mut Circuit,
    src: &[&QReg],
    s: &[QReg],
    dec: bool,
) {
    use crate::point_add::trailmix_port::arith::ripple_add::add_const;
    let n = src.len();
    if n == 0 {
        return;
    }
    let pbl = circ.push_section("p.bitlen");
    debug_assert!(
        (n as u64) <= (1u64 << (s.len().saturating_sub(1))),
        "bit_length_ctz_inplace: s width {} too small for n={n}",
        s.len()
    );
    let add_n = |circ: &mut Circuit| {
        let bytes: Vec<u8> = (0..s.len().div_ceil(8))
            .map(|i| (n >> (8 * i)) as u8)
            .collect();
        add_const(circ, s, &bytes);
    };
    let flip_to_complement_plus_n = |circ: &mut Circuit| {
        for q in s {
            circ.x(q);
        }
        add_n(circ);
    };

    if dec {
        // PRE: s = n. The middle bitlength primitive maps s to p = bitlen(src)-1.
        bit_length_lean_middle(circ, src, s, |_| false);
        // Exact affine map p -> n - 1 - p = ctz(original q).
        flip_to_complement_plus_n(circ);
    } else {
        // Inverse: ctz -> p, then undo the middle deposit p -> n.
        flip_to_complement_plus_n(circ);
        bit_length_lean_middle(circ, src, s, |_| false);
    }
    circ.pop_section(&pbl);
}

/// `p + 1` (secp256k1 base field prime) as 33 LE bytes.
fn p_plus_1_bytes() -> Vec<u8> {
    vec![
        0x30, 0xfc, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00,
    ]
}

/// Controlled field-negate `a := (p - a) mod p` IFF `g` (a in [0,p), 257-bit).
/// Self-inverse. `~a + (p+1) ≡ p - a (mod 2^257)`; canonical for a in [1,p).
/// (Relocated from `kaliski_spooky::unpacked` so `shrunken_pz` has no spooky-Kaliski dep.)
pub fn controlled_field_neg(c: &mut Circuit, g: &QReg, a: &[QReg]) {
    use crate::point_add::trailmix_port::arith::const_add::controlled_add_const;
    for q in a {
        c.cx(g, q);
    }
    controlled_add_const(c, g, a, &p_plus_1_bytes());
}

/// `s += bitlen(a) - bitlen(b)` (clz diff), bound by `bound`. After alignment in
/// the division substep, s is the shift to apply. Inverse: swap a,b.
/// LEAN `bit_length`: `s += bitlen(src)` (or `-=` if dec), via a reversible
/// prefix-AND ladder + gray-code deposit -- ~2n ccx (ladder build+unbuild) with
/// NO per-row position-equality. Supersedes the first-hit scan (~38 tof/row from
/// the per-row `toggle_on_cursor_eq_const` uncompute of `is_hit`).
///
/// Construction (MSB-first running flag `f_i` = "no 1 bit strictly above i"):
///   - prefix-AND ladder over ~src (X-bracketed) gives every `f_i` as a ladder
///     qubit, fully reversibly (fwd builds, rev unbuilds).
///   - deposit pos (init = n) ^= (i ^ (i+1)) gated on `f_i`, for i = n-1..0. The
///     gray differences telescope: pos collapses to the MSB index p (= bitlen-1).
///   - s += (pos + 1)  [bitlen]; then uncompute pos (re-run deposit) + ladder.
///
/// PRE: src nonzero (EEA gcd / nonzero quotient pad). For src==0 this returns
/// bitlen=1 (pos stays 0, +1); callers must not pass an all-zero src.
/// _middle core. Builds the prefix-AND ladder over ~src, deposits the MSB index
/// (= bitlen-1) into the caller's `pos` register (PRE: pos = |n>) in the FORWARD
/// sweep, runs `body` (which sees pos = MSB index), then unbuilds.
///
/// `body` returns whether the deposit should be UNDONE on the reverse sweep:
///   - `false` (DEFAULT, 3n): pos is KEPT at the MSB index -- the caller owns it
///     and must clear it later (e.g. via the SM's reverse). One consume = 3n.
///   - `true` (4n): the deposit is re-run on the reverse, returning pos to |n>.
///     Use when pos is a throwaway temp whose value was folded elsewhere in body.
///
/// The gray-code deposit is pure XOR (CX gated on a single flag materialized from
/// the prefix-AND with one ccx, then HMR-freed) -- so each consume is 1 toffoli
/// per position. Prefix build+unbuild = 2n; consume = n/sweep.
fn bit_length_lean_middle(
    circ: &mut Circuit,
    src: &[&QReg],
    pos: &[QReg],
    body: impl FnOnce(&mut Circuit) -> bool,
) {
    // Callbacks here consume only the deposited position and independent
    // metadata. They do not inspect the prefix network's borrowed inputs.
    if std::env::var("MIDQ_CHUNKED_PREFIX").ok().as_deref() == Some("1")
        && chunked_bitlength::fits(circ, src.len())
    {
        chunked_bitlength::xor(circ, src, pos);
        if body(circ) { chunked_bitlength::xor(circ, src, pos); }
        return;
    }
    use crate::point_add::trailmix_port::arith::khattar_gidney::{
        kg_prefix_ancilla_count, kg_prefix_compact_ancilla_count, KgPrefixAnd,
    };
    let n = src.len();
    if n == 0 {
        body(circ);
        return;
    }
    // ~src (X-bracket); the prefix-AND reads the complemented bits.
    for q in src {
        circ.x(q);
    }
    // q = ~src MSB-first: q[j] = ~src[n-1-j]. The log*-ancilla KG streaming
    // prefix-AND gives, at layer i, AND(ctrls) = AND(q[0..i]) = "no 1 in top i
    // positions" = f_k ("no 1 strictly above k") for k = n-1-i. ctrls is 1-2 qubits
    // (KG conditionally-clean form), so the deposit is the KG prefix-controlled-X
    // consumer directly: CX (1 ctrl, zero toffoli) or CCX (2 ctrls) per gray bit --
    // NO mcx materialize. Total ~3n-4n (2n prefix compute + n-2n consume).
    let qbits: Vec<&QReg> = src.iter().rev().copied().collect();
    let nanc = kg_prefix_ancilla_count(n);
    let anc_count = if lowq_compact_kganc_enabled() {
        kg_prefix_compact_ancilla_count(n)
    } else {
        nanc
    };
    let anc_owned = circ.alloc_qreg_bits("bll.kganc", anc_count);
    let flag = (!lowq_one_a_elim_enabled()).then(|| circ.alloc_qreg("bll.flag"));
    // Deposit at layer i (position k = n-1-i): gray-XOR (k ^ (k+1)) into pos gated
    // on f_k = AND(ctrls). For two controls, use the first target as a borrowed
    // fanout pivot: CNOT it into the other targets, toggle it with one CCX, then
    // undo the fanout. Every target receives f_k, the pivot's unknown input is
    // restored out of the others, and no clean flag qubit is needed. For <=1 ctrl
    // the gray bits are direct CX/X. pos starts at |n>; the gray differences
    // telescope it to the MSB index p. Self-inverse, so reverse undoes pos to |n>.
    fn deposit_step(
        circ: &mut Circuit,
        i: usize,
        ctrls: &[&QReg],
        pos: &[QReg],
        flag: Option<&QReg>,
        n: usize,
    ) {
        if i >= n {
            return; // i == n is the empty (k = -1) layer
        }
        let k = n - 1 - i;
        let gd = k ^ (k + 1);
        let bits: Vec<usize> = (0..pos.len()).filter(|&b| (gd >> b) & 1 == 1).collect();
        if bits.is_empty() {
            return;
        }
        match ctrls {
            [] => {
                for &b in &bits {
                    circ.x(&pos[b]);
                }
            }
            [c] => {
                for &b in &bits {
                    circ.cx(c, &pos[b]);
                }
            }
            [a, b2] => {
                if let Some(flag) = flag {
                    circ.ccx(a, b2, flag);
                    for &bit in &bits {
                        circ.cx(flag, &pos[bit]);
                    }
                    circ.clear_and(flag, a, b2);
                } else {
                    let pivot = &pos[bits[0]];
                    for &bit in &bits[1..] {
                        circ.cx(pivot, &pos[bit]);
                    }
                    circ.ccx(a, b2, pivot);
                    for &bit in &bits[1..] {
                        circ.cx(pivot, &pos[bit]);
                    }
                }
            }
            _ => unreachable!("KG prefix ctrls is <=2 qubits"),
        }
    }

    let anc: Vec<&QReg> = anc_owned.iter().collect();
    let kg = if lowq_compact_kganc_enabled() {
        drop(anc);
        KgPrefixAnd::new_compact_refs(&qbits, &anc_owned)
    } else {
        KgPrefixAnd::new(&qbits, &anc)
    };
    let done = kg.forward(circ, |c, i, ctrls| {
        deposit_step(c, i, ctrls, pos, flag.as_ref(), n)
    }); // pos -> p
    let clean = body(circ);
    if clean {
        // 4n: re-run the deposit on the reverse, returning pos to |n>.
        done.reverse(circ, |c, i, ctrls| {
            deposit_step(c, i, ctrls, pos, flag.as_ref(), n)
        });
    } else {
        // 3n: unbuild the prefix only; pos stays at the MSB index (caller-owned).
        done.reverse(circ, |_, _, _| {});
    }
    if let Some(flag) = flag {
        circ.zero_and_free(flag);
    }
    for q in anc_owned {
        circ.zero_and_free(q);
    }
    for q in src {
        circ.x(q);
    }
}

/// `s += bitlen(src)` (or `-=` if dec). Built from [`bit_length_lean_middle`]:
/// pos = MSB index in the middle, then `s ±= (pos + 1)`. With `dec` this clears a
/// register `s` that already holds `bitlen(src)` (the "same method" both ways).
fn bit_length_lean(
    circ: &mut Circuit,
    src: &[&QReg],
    s: &[QReg],
    dec: bool,
    borrowed_carry: Option<&QReg>,
) {
    let n = src.len();
    if n == 0 {
        return;
    }
    let pbl = circ.push_section("p.bitlen");
    // pos holds transient gray values up to (n-1)^n < 2n; reuse s's width (equal-
    // width so the Cuccaro add s += pos is clean).
    let pos_w = s.len();
    debug_assert!(
        (n as u64) <= (1u64 << (pos_w - 1)),
        "bit_length_lean: s width {pos_w} too small for n={n}"
    );
    let pos = circ.alloc_qreg_bits("bll.pos", pos_w);
    xor_const(circ, &pos, n); // pos = n  (PRE for the middle)
    bit_length_lean_middle(circ, src, &pos, |circ| {
        // pos = MSB index = bitlen-1; s ±= (pos + 1).
        if dec {
            for q in s {
                circ.x(q);
            }
        }
        let pref: Vec<&QReg> = pos.iter().collect();
        let sref: Vec<&QReg> = s.iter().collect();
        add_refs(circ, &sref, &pref, borrowed_carry); // s += pos
        if lowq_one_a_elim_enabled() {
            // Keep the increment unconditional so a second fixed-one wrapper
            // cannot bind the peak after sm.one_a is removed.
            use crate::point_add::trailmix_port::arith::khattar_gidney::inc_khattar_gidney;
            inc_khattar_gidney(circ, s); // s += 1  (bitlen = p + 1)
        } else {
            let one = circ.alloc_qreg("bll.one");
            circ.x(&one);
            ctrl_inc(circ, &one, s);
            circ.x(&one);
            circ.zero_and_free(one);
        }
        if dec {
            for q in s {
                circ.x(q);
            }
        }
        true // pos is a throwaway temp -> clean on reverse (4n)
    });
    xor_const(circ, &pos, n); // pos back to |0>
    for q in pos {
        circ.zero_and_free(q);
    }
    circ.pop_section(&pbl);
}

fn lowq_clz_diff_const_fold_enabled() -> bool {
    if std::env::var("LOWQ_CLZ_DIFF_CONST_FOLD").ok().as_deref() != Some("1") {
        return false;
    }
    let target = std::env::var("TRAILMIX_Q_TARGET")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .expect("LOWQ_CLZ_DIFF_CONST_FOLD requires an integer TRAILMIX_Q_TARGET");
    assert!(
        matches!(target, 683 | 684 | 685),
        "LOWQ_CLZ_DIFF_CONST_FOLD is sealed to Q_TARGET 683/684/685"
    );
    true
}

/// `_middle` form of the clz-diff compute-USE-uncompute pattern: deposits the two
/// bitlen positions into the internal `pa`/`pb` ancillae, FOLDS the diff
/// d = bitlen(a)-bitlen(b) (windowed) INTO `pa`, runs `body(circ, &pa)` with `pa`
/// holding the diff, then restores `pa` and un-deposits to |0>. No caller-supplied
/// diff register -- `pa` IS the diff, so nothing extra is live at the peak (this is
/// the `shrunken_pz_divide_forward` peak section). `w` sizes pa/pb (must hold the window MSB
/// index and the signed diff). Scans un-nested (one KG ancilla set live at a time).
fn clz_fuse_div_a_enabled() -> bool {
    std::env::var("TRAILMIX_FUSE_DIV_CLZ_A").ok().as_deref() == Some("1")
}

/// Signed constant add into a w-wide register (was the `add_pa` closure).
fn clz_add_const_signed(circ: &mut Circuit, pa: &[QReg], v: i64, w: usize) {
    use crate::point_add::trailmix_port::arith::ripple_add::add_const;
    let val = i128::from(v).rem_euclid(1i128 << w) as u128;
    let bytes: Vec<u8> = (0..w.div_ceil(8)).map(|i| (val >> (8 * i)) as u8).collect();
    add_const(circ, pa, &bytes);
}

/// Deposit pos_a = bit-length(A[lo_a..]) into a fresh `pa` register (self-inverse
/// deposit). Caller holds `pa` and clears it with `clz_undeposit_a`. Hoisting this
/// out of the two per-step clz calls (A is unchanged between them, only B rotates)
/// removes one redundant A bit-length scan per division step (TRAILMIX_FUSE_DIV_CLZ_A).
fn clz_deposit_a(circ: &mut Circuit, a: &[QReg], w: usize, lo_a: usize) -> Vec<QReg> {
    let aw: Vec<&QReg> = a[lo_a..a.len()].iter().collect();
    let na = aw.len();
    let pa = circ.alloc_qreg_bits("clzm.pa", w);
    xor_const(circ, &pa, na);
    bit_length_lean_middle(circ, &aw, &pa, |_| false); // pa = pos_a
    pa
}

/// Inverse of clz_deposit_a: restore pos_a -> |0> and free pa.
fn clz_undeposit_a(circ: &mut Circuit, pa: Vec<QReg>, a: &[QReg], lo_a: usize) {
    let aw: Vec<&QReg> = a[lo_a..a.len()].iter().collect();
    let na = aw.len();
    bit_length_lean_middle(circ, &aw, &pa, |_| false); // pa -> na
    xor_const(circ, &pa, na); // pa -> 0
    for q in pa {
        circ.zero_and_free(q);
    }
}

/// Given a pre-deposited pos_a in `pa`, deposit pos_b for B[lo_b..], fold the windowed
/// diff into pa, run `body(pa=diff)`, then unfold pa back to pos_a and clear pb.
/// pa is BORROWED (not deposited/freed here) so it can be reused across calls.
fn clz_diff_use(
    circ: &mut Circuit,
    pa: &[QReg],
    b: &[QReg],
    w: usize,
    lo_a: usize,
    lo_b: usize,
    borrowed_carry: Option<&QReg>,
    body: impl FnOnce(&mut Circuit, &[QReg]),
) {
    let bw: Vec<&QReg> = b[lo_b..b.len()].iter().collect();
    let nb = bw.len();
    let pb = circ.alloc_qreg_bits("clzm.pb", w);
    xor_const(circ, &pb, nb);
    bit_length_lean_middle(circ, &bw, &pb, |_| false); // pb = pos_b

    clz_diff_positions(circ, pa, &pb, lo_a, lo_b, borrowed_carry, body);
    bit_length_lean_middle(circ, &bw, &pb, |_| false);
    xor_const(circ, &pb, nb);
    for q in pb {
        circ.zero_and_free(q);
    }
}

fn clz_diff_positions(
    circ: &mut Circuit,
    pa: &[QReg],
    pb: &[QReg],
    lo_a: usize,
    lo_b: usize,
    borrowed_carry: Option<&QReg>,
    body: impl FnOnce(&mut Circuit, &[QReg]),
) {
    let w = pa.len();
    let const_fold = lowq_clz_diff_const_fold_enabled();
    if const_fold {
        {
            let par: Vec<&QReg> = pa.iter().collect();
            let pbr: Vec<&QReg> = pb.iter().collect();
            sub_refs(circ, &par, &pbr);
        }
        clz_add_const_signed(circ, pa, lo_a as i64 - lo_b as i64, w);
    } else {
        {
            let par: Vec<&QReg> = pa.iter().collect();
            let pbr: Vec<&QReg> = pb.iter().collect();
            clz_add_const_signed(circ, pa, 1 + lo_a as i64, w);
            sub_refs(circ, &par, &pbr);
        }
        clz_add_const_signed(circ, pa, -(1 + lo_b as i64), w);
    }

    body(circ, pa); // USE pa (= diff)

    if const_fold {
        {
            let par: Vec<&QReg> = pa.iter().collect();
            let pbr: Vec<&QReg> = pb.iter().collect();
            add_refs(circ, &par, &pbr, borrowed_carry);
        }
        clz_add_const_signed(circ, pa, lo_b as i64 - lo_a as i64, w);
    } else {
        clz_add_const_signed(circ, pa, 1 + lo_b as i64, w);
        {
            let par: Vec<&QReg> = pa.iter().collect();
            let pbr: Vec<&QReg> = pb.iter().collect();
            add_refs(circ, &par, &pbr, borrowed_carry);
        }
        clz_add_const_signed(circ, pa, -(1 + lo_a as i64), w);
    }

}

/// _middle clz-diff: deposit pos_a, fold diff, run body, restore. Flag-off path is
/// EXACTLY the deposit_a/diff_use/undeposit_a sequence (gate-identical to the prior
/// monolithic impl); the substeps reuse a hoisted pos_a under TRAILMIX_FUSE_DIV_CLZ_A.
fn clz_diff_body_middle(
    circ: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    w: usize,
    lo_a: usize,
    lo_b: usize,
    borrowed_carry: Option<&QReg>,
    body: impl FnOnce(&mut Circuit, &[QReg]),
) {
    let pbl = circ.push_section("p.bitlen");
    let pa = clz_deposit_a(circ, a, w, lo_a);
    clz_diff_use(circ, &pa, b, w, lo_a, lo_b, borrowed_carry, body);
    clz_undeposit_a(circ, pa, a, lo_a);
    circ.pop_section(&pbl);
}

fn clz_offset_from_hoisted_a(
    circ: &mut Circuit,
    pa: &[QReg],
    b: &[QReg],
    lo_a: usize,
    lo_b: usize,
    active: GateControl<'_>,
    offset: &QReg,
) {
    let bw: Vec<&QReg> = b[lo_b..].iter().collect();
    let n = bw.len();
    let parity = circ.alloc_qreg_bits("clz.parity", 1);
    xor_const(circ, &parity, n);
    // The XOR deposit may be restricted to its low output bit exactly.
    bit_length_lean_middle(circ, &bw, &parity, |_| false);
    circ.cx(&pa[0], &parity[0]);
    xor_const(circ, &parity, lo_a ^ lo_b);
    with_peak_gate_control(circ, active, |circ, gate| {
        circ.ccx(gate, &parity[0], offset);
    });
    xor_const(circ, &parity, lo_a ^ lo_b);
    circ.cx(&pa[0], &parity[0]);
    bit_length_lean_middle(circ, &bw, &parity, |_| false);
    xor_const(circ, &parity, n);
    for bit in parity {
        circ.zero_and_free(bit);
    }
}

pub(crate) fn midq_clz_parity_selftest() {
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update}, Shake256};
    let mut checked = 0usize;
    for width in 2..=8 {
        for lo_b in [0, 1, width / 2] {
            let make = |compact: bool| {
                let mut circ = Circuit::new();
                let pa = circ.alloc_qreg_bits("test.pa", 5);
                let value = circ.alloc_qreg_bits("test.value", width);
                let active = circ.alloc_qreg("test.active");
                let offset = circ.alloc_qreg("test.offset");
                let ids: Vec<_> = pa.iter().chain(value.iter())
                    .chain([&active, &offset])
                    .map(|q| QubitId(q.id().into())).collect();
                let gate = GateControl::Direct(&active);
                // Choose distinct low-window origins to also test constant parity.
                let lo_a = (lo_b + 1) % width;
                if compact {
                    clz_offset_from_hoisted_a(
                        &mut circ, &pa, &value, lo_a, lo_b, gate, &offset);
                } else {
                    let carry = circ.alloc_qreg("test.carry");
                    clz_diff_use(&mut circ, &pa, &value, 5, lo_a, lo_b, Some(&carry),
                        |circ, diff| circ.ccx(&active, &diff[0], &offset));
                    circ.zero_and_free(carry);
                }
                (circ.b.ops.clone(), ids)
            };
            let (original, original_ids) = make(false);
            let (compact, compact_ids) = make(true);
            let run = |ops: &[crate::circuit::Op], ids: &[QubitId], first: usize| {
                let (nq, nb, _, _) = analyze_ops(ops.iter());
                let mut seed = Shake256::default();
                seed.update(b"midq-clz-parity-component-v1");
                seed.update(&first.to_le_bytes());
                let mut rng = seed.finalize_xof();
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
                for (index, &id) in ids.iter().enumerate() {
                    for shot in 0..64 {
                        if (first + shot) >> index & 1 == 1 {
                            *sim.qubit_mut(id) |= 1u64 << shot;
                        }
                    }
                }
                sim.apply_iter(ops.iter());
                assert_eq!(sim.phase, 0, "phase error at width={width}, lo={lo_b}");
                let output: Vec<_> = ids.iter().map(|&id| sim.qubit(id)).collect();
                for &id in ids { *sim.qubit_mut(id) = 0; }
                assert!(sim.qubits.iter().all(|&mask| mask == 0), "dirty scratch");
                output
            };
            for first in (0..1usize << original_ids.len()).step_by(64) {
                assert_eq!(run(&original, &original_ids, first), run(&compact, &compact_ids, first),
                    "offset parity mismatch at width={width}, lo={lo_b}, batch={first}");
                checked += 64;
            }
        }
    }
    eprintln!("MIDQ_CLZ_PARITY_SELFTEST PASS: {checked} exhaustive inputs, value/phase/ancilla");
}

/// Rotate-LEFT `reg` in place by the quantum amount `s` (= reg << s, since the
/// aligned value's bitlen <= reg width so no nonzero bit wraps). Uses the ACYCLIC
/// `barrel_shift_inplace` (exactly `s.len()` layers, no wrap) rather than
/// `controlled_cyclic_rotate` (s.len()+1 full-width layers incl. a spurious
/// offset layer, + cyclic wrap churn): ~1.28x fewer cswaps. The no-wrap
/// precondition (top s bits of reg are |0>) is exactly the existing one.
/// forward=true is `<< s`; forward=false (restore) is `>> s`, Fredkin self-inverse.
fn rotate_left(circ: &mut Circuit, reg: &[QReg], s: &[QReg]) {
    crate::point_add::trailmix_port::arith::qshift_sub::barrel_shift_inplace(circ, reg, s, true);
}
fn rotate_right(circ: &mut Circuit, reg: &[QReg], s: &[QReg]) {
    crate::point_add::trailmix_port::arith::qshift_sub::barrel_shift_inplace(circ, reg, s, false);
}

/// `q[i] ^= active AND (s == i)` = `q ^= active·(1<<s)` -- the q-demux via KG
/// `unary_iterate_log_star` (~2 ccx/step) instead of a per-bit `eq_const_inplace` loop
/// (~58 tof/bit, ~30x more). active=0 => s masked to 0 => only i=0 gate fires,
/// `ANDed` with active=0 -> no-op. Self-inverse; `s` restored on exit.
fn set_bit_at_s_gated(circ: &mut Circuit, q_div: &[QReg], s: &[QReg], active: &QReg) {
    use crate::point_add::trailmix_port::arith::khattar_gidney::unary_iterate_log_star;
    let n_pad = q_div.len();
    if n_pad == 0 {
        return;
    }
    let prev = circ.push_section("p.demux");
    let sref: Vec<&QReg> = s.iter().collect();
    unary_iterate_log_star(circ, &sref, n_pad, |c, i, gate| {
        c.ccx(active, gate, &q_div[i]);
    });
    circ.pop_section(&prev);
}

/// Unconditional `a -= b` (mod 2^len) via two's complement (X-bracket + add).
fn sub_refs(circ: &mut Circuit, a: &[&QReg], b: &[&QReg]) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::ctrl_sub;
    let one = circ.alloc_qreg("sm.one");
    circ.x(&one);
    ctrl_sub(circ, &one, a, b); // gated on |1> = unconditional
    circ.x(&one);
    circ.zero_and_free(one);
}

/// Controlled decrement `s -= 1` iff `g` (X-bracket + controlled increment).
fn ctrl_dec(circ: &mut Circuit, g: &QReg, s: &[QReg]) {
    use crate::point_add::trailmix_port::arith::khattar_gidney::cinc_khattar_gidney;
    for q in s {
        circ.x(q);
    }
    cinc_khattar_gidney(circ, s, g); // a=s, ctrl=g
    for q in s {
        circ.x(q);
    }
}

/// Controlled increment `s += 1` iff `g`.
fn ctrl_inc(circ: &mut Circuit, g: &QReg, s: &[QReg]) {
    use crate::point_add::trailmix_port::arith::khattar_gidney::cinc_khattar_gidney;
    cinc_khattar_gidney(circ, s, g);
}

/// Unconditional `a += b` (mod 2^len), specialized directly from the
/// control-|1> Cuccaro path so no fixed-one control qubit is needed.
fn add_refs(circ: &mut Circuit, a: &[&QReg], b: &[&QReg], borrowed_carry: Option<&QReg>) {
    use crate::point_add::trailmix_port::arith::cuccaro::{
        add_cuccaro_3n_uncontrolled_refs, add_cuccaro_3n_uncontrolled_refs_with_carry,
    };
    let prev = circ.push_section("p.add");
    if lowq_one_a_elim_enabled() {
        if lowq_borrow_passenger_carry_enabled() {
            add_cuccaro_3n_uncontrolled_refs_with_carry(
                circ,
                a,
                b,
                borrowed_carry.expect("combined low-Q route requires a passenger carry"),
            );
        } else {
            add_cuccaro_3n_uncontrolled_refs(circ, a, b);
        }
    } else {
        use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::ctrl_add;
        let one = circ.alloc_qreg("sm.one_a");
        circ.x(&one);
        ctrl_add(circ, &one, a, b);
        circ.x(&one);
        circ.zero_and_free(one);
    }
    circ.pop_section(&prev);
}

/// Unpacked PZ state-machine registers. gcd pair (`a_gcd=A`, `b_gcd=B`) shrinks;
/// cofactor pair (ca=|a|, cb=|b|) grows. `q_div/q_mul` are the quotient pads
/// (~one quotient, ~26 bits each): `q_div` is built by the division (`q_div^=1`<<s),
/// swapped to `q_mul`, and DRAINED by the multiply (a += b<<`ctz(q_mul)`, clearing
/// it) -- the pipelined drain is what keeps the quotient record at one-quotient
/// size instead of a full ~256-bit tape. NOT removable (scripts/
/// `pz_fused_nopad_proto.py`: fusing gives the right inverse but s-recovery from
/// the cofactors mismatches ~30%, and an undrained pad accumulates a full tape).
pub struct PzSmRegs {
    pub a_gcd: Vec<QReg>,
    pub b_gcd: Vec<QReg>,
    pub ca: Vec<QReg>,
    pub cb: Vec<QReg>,
    pub q_div: Vec<QReg>,
    pub q_mul: Vec<QReg>,
}

/// Single-qubit state flags + sign. Invariant matches `pz_big_step`.
pub struct PzSmFlags {
    pub div_active: QReg,
    pub mul_active: QReg,
    pub offset: QReg,
    pub parity: QReg,
    pub sgn: QReg,
}

/// Load/unload the classical constant `c` into `reg` via X gates (self-inverse).
fn xor_const(circ: &mut Circuit, reg: &[QReg], c: usize) {
    for (j, q) in reg.iter().enumerate() {
        if (c >> j) & 1 == 1 {
            circ.x(q);
        }
    }
}

/// Magnitude compare `out ^= (a < b)` narrowed to the schedule window
/// `[lo, min(a.len, b.len))`. Used for the ALIGNED offset/o compares where a and
/// b share a bitlen (MSB guaranteed in [lo, hi) by the schedule), so the top bits
/// decide the order; a tie below `lo` (prob ~2^-(hi-lo) per the window width)
/// flips the result -- within the whole-pass tail tolerance. Forward and inverse
/// substeps call this with the same `lo`, so the (possibly-wrong) flag is
/// computed identically both ways and round-trips cleanly. Restores a,b.
/// NOT for the magnitude GATES (`g_mul/g_div)`: there A,B get arbitrarily close at
/// the div<->mul transition, so a deep tie is common, not a 2^-w tail.
fn narrow_lt(circ: &mut Circuit, a: &[QReg], b: &[QReg], out: &QReg, lo: usize) {
    let hi = a.len().min(b.len());
    let lo = lo.min(hi.saturating_sub(1));
    let ar: Vec<&QReg> = a[lo..hi].iter().collect();
    let br: Vec<&QReg> = b[lo..hi].iter().collect();
    borrow_compare_refs(circ, &ar, &br, out);
}

fn clear_narrow_lt(circ: &mut Circuit, a: &[QReg], b: &[QReg], out: &QReg, lo: usize) {
    let hi = a.len().min(b.len());
    let lo = lo.min(hi.saturating_sub(1));
    let ar: Vec<&QReg> = a[lo..hi].iter().collect();
    let br: Vec<&QReg> = b[lo..hi].iter().collect();
    clear_borrow_compare_refs(circ, &ar, &br, out);
}

/// WINDOWED division substep: same as `division_substep_act` but the two clz
/// computations scan only the schedule's clz windows (`lo_a`/`lo_b` = window low
/// bounds for A/B) and the B<<s / restore rotates use `rot_bits` shift bits
/// (shift bound) instead of the full `s_rot` width. The offset-clean clz operates
/// on (A, `B_aligned`), both ~bitlen(A), so it reuses the A window (`lo_a`). For
/// in-schedule inputs this is gate-identical to `division_substep_act`.
#[allow(clippy::too_many_arguments)]
pub fn division_substep_windowed(
    circ: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    q_div: &[QReg],
    s_rot: &[QReg],
    offset: &QReg,
    active: GateControl<'_>,
    borrowed_carry: Option<&QReg>,
    lo_a: usize,
    lo_b: usize,
    rot_bits: usize,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::ctrl_sub;
    let aref: Vec<&QReg> = a.iter().collect();
    let bref: Vec<&QReg> = b.iter().collect();
    let n_pad = q_div.len();
    let rb = rot_bits.min(s_rot.len());
    let w = s_rot.len();

    if std::env::var("MIDQ_RETAIN_DIV_LENGTHS").ok().as_deref() == Some("1") {
        return division_substep_retained_lengths(circ, a, b, q_div, s_rot,
            offset, active, borrowed_carry, lo_a, lo_b, rot_bits, false);
    }

    // The two CLZ blocks observe the same A. Hoist its deposited bit-length
    // across both blocks so only B is rescanned after alignment.
    let pa_hoist = if clz_fuse_div_a_enabled() {
        if let GateControl::Hybrid(control) = active {
            control.release(circ);
        }
        Some(clz_deposit_a(circ, a, w, lo_a))
    } else {
        None
    };

    // diff = bitlen(A)-bitlen(B) (windowed _middle, folded into the clz's own pa);
    // mask s_rot = diff AND active.
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| {
                for (j, bit) in diff.iter().enumerate() {
                    circ.ccx(g, bit, &s_rot[j]);
                }
            });
        };
        if let Some(pa) = &pa_hoist {
            clz_diff_use(circ, pa, b, w, lo_a, lo_b, borrowed_carry, use_diff);
        } else {
            clz_diff_body_middle(circ, a, b, w, lo_a, lo_b, borrowed_carry, use_diff);
        }
    });

    rotate_left(circ, b, &s_rot[0..rb]); // B <<= s if active (bounded rotator)

    // offset = active AND (A < B_aligned) -- narrowed (A,B_aligned share bitlen).
    {
        let or = circ.alloc_qreg("dg.offr");
        narrow_lt(circ, a, b, &or, lo_a);
        with_gate_control(circ, active, |circ, g| circ.ccx(g, &or, offset));
        clear_narrow_lt(circ, a, b, &or, lo_a);
        circ.zero_and_free(or);
    }
    rotate_right(circ, b, std::slice::from_ref(offset)); // B >>= 1 if offset
    ctrl_dec(circ, offset, s_rot); // s_rot -= 1 if offset => s_eff

    // clean offset via windowed _middle clz on (A, B_aligned) -> A window. The diff
    // lives in the clz's pa (this clz is the shrunken_pz_divide_forward peak section).
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| circ.ccx(g, &diff[0], offset));
        };
        if let Some(pa) = &pa_hoist {
            if std::env::var("MIDQ_CLZ_OFFSET_PARITY").ok().as_deref() == Some("1") {
                clz_offset_from_hoisted_a(circ, pa, b, lo_a, lo_a, active, offset);
            } else {
                clz_diff_use(circ, pa, b, w, lo_a, lo_a, borrowed_carry, use_diff);
            }
        } else {
            clz_diff_body_middle(circ, a, b, w, lo_a, lo_a, borrowed_carry, use_diff);
        }
        if let Some(pa) = pa_hoist {
            clz_undeposit_a(circ, pa, a, lo_a);
        }
    });

    with_gate_control(circ, active, |circ, g| {
        ctrl_sub(circ, g, &aref, &bref); // A -= B_aligned if active
    });

    with_gate_control(circ, active, |circ, g| {
        set_bit_at_s_gated(circ, q_div, s_rot, g); // q_div ^= active·(1<<s_rot)
    });

    rotate_right(circ, b, &s_rot[0..rb]); // restore B >>= s_eff (bounded rotator)

    // clean s_rot via ctz(q_div) gated on active (q small -> no window). Local ctz
    // accumulator (freed before the next step; off the clz peak).
    {
        let t = circ.alloc_qreg_bits("dg.ctz", w);
        xor_const(circ, &t, n_pad);
        let rev: Vec<&QReg> = q_div.iter().rev().collect();
        bit_length_ctz(circ, active, &rev, &t, true, borrowed_carry);
        let srr: Vec<&QReg> = s_rot.iter().collect();
        let tr: Vec<&QReg> = t.iter().collect();
        with_ctz_gate_control(circ, active, |circ, g| ctrl_sub(circ, g, &srr, &tr));
        bit_length_ctz(circ, active, &rev, &t, false, borrowed_carry);
        xor_const(circ, &t, n_pad);
        for q in t {
            circ.zero_and_free(q);
        }
    }
}

/// Gate-by-gate INVERSE of `division_substep_windowed` (for the backward pass).
/// Reverses the op sequence; the compute-use-uncompute blocks (clz-mask, offset,
/// offset-clean, q-demux) are self-inverse and run as-is; `rotate_left`<->right,
/// ctrl_sub->ctrl_add, ctrl_dec->ctrl_inc flip. Restores A += B<<`s_eff`, clears
/// the `q_div` bit, leaving `A/B/q_div/s/s_rot/offset` as before the forward step.
#[allow(clippy::too_many_arguments)]
pub fn division_substep_windowed_inv(
    circ: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    q_div: &[QReg],
    s_rot: &[QReg],
    offset: &QReg,
    active: GateControl<'_>,
    borrowed_carry: Option<&QReg>,
    lo_a: usize,
    lo_b: usize,
    rot_bits: usize,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::ctrl_add;
    let aref: Vec<&QReg> = a.iter().collect();
    let bref: Vec<&QReg> = b.iter().collect();
    let n_pad = q_div.len();
    let rb = rot_bits.min(s_rot.len());
    let w = s_rot.len();

    if std::env::var("MIDQ_RETAIN_DIV_LENGTHS").ok().as_deref() == Some("1") {
        return division_substep_retained_lengths(circ, a, b, q_div, s_rot,
            offset, active, borrowed_carry, lo_a, lo_b, rot_bits, true);
    }

    // 12' s_rot clean inverse: ctrl_sub -> ctrl_add. Local ctz accumulator.
    {
        let t = circ.alloc_qreg_bits("dg.ctz", w);
        xor_const(circ, &t, n_pad);
        let rev: Vec<&QReg> = q_div.iter().rev().collect();
        bit_length_ctz(circ, active, &rev, &t, true, borrowed_carry);
        let srr: Vec<&QReg> = s_rot.iter().collect();
        let tr: Vec<&QReg> = t.iter().collect();
        with_ctz_gate_control(circ, active, |circ, g| ctrl_add(circ, g, &srr, &tr));
        bit_length_ctz(circ, active, &rev, &t, false, borrowed_carry);
        xor_const(circ, &t, n_pad);
        for q in t {
            circ.zero_and_free(q);
        }
    }
    // 11' rotate_left (was rotate_right restore).
    rotate_left(circ, b, &s_rot[0..rb]);
    // 10' q_div demux (self-inverse XOR).
    with_gate_control(circ, active, |circ, g| {
        set_bit_at_s_gated(circ, q_div, s_rot, g); // q_div ^= active·(1<<s_rot)
    });
                                                    // 9' ctrl_sub -> ctrl_add (restore A += B_aligned).
    with_gate_control(circ, active, |circ, g| ctrl_add(circ, g, &aref, &bref));

    // Only now is A restored to the state observed by both inverse CLZ blocks.
    let pa_hoist = if clz_fuse_div_a_enabled() {
        if let GateControl::Hybrid(control) = active {
            control.release(circ);
        }
        Some(clz_deposit_a(circ, a, w, lo_a))
    } else {
        None
    };

    // 8' offset clean (self-inverse, _middle); diff in the clz's pa.
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| circ.ccx(g, &diff[0], offset));
        };
        if let Some(pa) = &pa_hoist {
            if std::env::var("MIDQ_CLZ_OFFSET_PARITY").ok().as_deref() == Some("1") {
                clz_offset_from_hoisted_a(circ, pa, b, lo_a, lo_a, active, offset);
            } else {
                clz_diff_use(circ, pa, b, w, lo_a, lo_a, borrowed_carry, use_diff);
            }
        } else {
            clz_diff_body_middle(circ, a, b, w, lo_a, lo_a, borrowed_carry, use_diff);
        }
    });
    // 7' ctrl_dec -> ctrl_inc.
    ctrl_inc(circ, offset, s_rot);
    // 6' rotate_left (was rotate_right by offset).
    rotate_left(circ, b, std::slice::from_ref(offset));
    // 5' offset compute (self-inverse) -- narrowed, same window as forward.
    {
        let or = circ.alloc_qreg("dg.offr");
        narrow_lt(circ, a, b, &or, lo_a);
        with_gate_control(circ, active, |circ, g| circ.ccx(g, &or, offset));
        clear_narrow_lt(circ, a, b, &or, lo_a);
        circ.zero_and_free(or);
    }
    // 4' rotate_right (was rotate_left B<<s).
    rotate_right(circ, b, &s_rot[0..rb]);
    // 3',2',1' clz-mask block (self-inverse, _middle) -- clears s_rot to |0>.
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| {
                for (j, bit) in diff.iter().enumerate() {
                    circ.ccx(g, bit, &s_rot[j]);
                }
            });
        };
        if let Some(pa) = &pa_hoist {
            clz_diff_use(circ, pa, b, w, lo_a, lo_b, borrowed_carry, use_diff);
        } else {
            clz_diff_body_middle(circ, a, b, w, lo_a, lo_b, borrowed_carry, use_diff);
        }
        if let Some(pa) = pa_hoist {
            clz_undeposit_a(circ, pa, a, lo_a);
        }
    });
}

/// `out ^= (reg != 0)` (restores reg).
fn or_nonzero(circ: &mut Circuit, reg: &[QReg], out: &QReg) {
    use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
    let prev = circ.push_section("p.ornz");
    for q in reg {
        circ.x(q);
    }
    let refs: Vec<&QReg> = reg.iter().collect();
    mcx_clean_k(circ, &refs, out); // out ^= (reg == 0)
    for q in reg {
        circ.x(q);
    }
    circ.x(out); // out ^= (reg != 0)
    circ.pop_section(&prev);
}

/// `out ^= (reg == 0)` via X-bracket + mcx (clean, self-inverse, restores reg).
fn or_is_zero(circ: &mut Circuit, reg: &[QReg], out: &QReg) {
    use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
    let prev = circ.push_section("p.orz");
    for q in reg {
        circ.x(q);
    }
    let refs: Vec<&QReg> = reg.iter().collect();
    mcx_clean_k(circ, &refs, out); // out ^= (reg == 0)
    for q in reg {
        circ.x(q);
    }
    circ.pop_section(&prev);
}

/// Clear a known zero/nonzero predicate, not an arbitrary XOR target.
/// PRE: out equals the indicated predicate of the CURRENT register. The
/// register may have changed since production only if its predicate did not.
fn clear_zero_predicate(circ: &mut Circuit, reg: &[QReg], out: &QReg, nonzero: bool) {
    if std::env::var("MIDQ_MEASURE_PREDICATE").ok().as_deref() != Some("1") {
        if nonzero {
            or_nonzero(circ, reg, out);
        } else {
            or_is_zero(circ, reg, out);
        }
        return;
    }
    use crate::point_add::trailmix_port::arith::khattar_gidney::phase_and_of_khattar_gidney_refs;
    let phase = circ.alloc_bit();
    circ.hmr(out, phase);
    circ.with_condition(phase, |circ| {
        let section = circ.push_section("p.or.phase");
        // HMR contributes (-1)^(m*f). For nonzero, f = 1 XOR [reg==0],
        // so include (-1)^m explicitly; even the branch-global phase cancels.
        if nonzero {
            phase_and_of_khattar_gidney_refs(circ, &[]);
        }
        for q in reg {
            circ.x(q);
        }
        let refs: Vec<&QReg> = reg.iter().collect();
        phase_and_of_khattar_gidney_refs(circ, &refs);
        for q in reg {
            circ.x(q);
        }
        circ.pop_section(&section);
    });
    circ.free_bit(phase);
}

#[path = "predicate_clear_selftest.rs"]
mod predicate_clear_selftest;
pub(crate) use predicate_clear_selftest::run as midq_predicate_clear_selftest;

/// WINDOWED multiply substep: same as `multiply_substep_act` but the two clz
/// computations scan the schedule's cofactor clz windows. The `o` clz is on
/// (ca, cb<<s2), both ~bitlen(ca) -> ca window (`ca_window`). The s_rot-clean clz is
/// on (cb, ca) -> cb/ca windows. The cb<<s2 / restore rotates use `rot_bits`.
/// q (ctz) is small -> not windowed. Gate-identical for in-schedule inputs.
#[allow(clippy::too_many_arguments)]
pub fn multiply_substep_windowed(
    circ: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    q_mul: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    active: GateControl<'_>,
    borrowed_carry: Option<&QReg>,
    ca_window: usize,
    cb_window: usize,
    rot_bits: usize,
) {
    if std::env::var("MIDQ_RETAIN_MUL_LENGTHS").ok().as_deref() == Some("1") {
        return division_substep_retained_lengths(circ, a, b, q_mul, s_rot,
            off, active, borrowed_carry, ca_window, cb_window, rot_bits, true);
    }
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};
    let aref: Vec<&QReg> = a.iter().collect();
    let bref: Vec<&QReg> = b.iter().collect();
    let n_pad = q_mul.len();
    let rb = rot_bits.min(s_rot.len());
    let w = s_rot.len();

    // s_rot = ctz(q_mul) AND active. Local ctz accumulator `t` (freed before the
    // clz peak; q small -> no window).
    {
        let t = circ.alloc_qreg_bits("mg.ctz", w);
        let rev: Vec<&QReg> = q_mul.iter().rev().collect();
        xor_const(circ, &t, n_pad);
        bit_length_ctz(circ, active, &rev, &t, true, borrowed_carry);
        with_ctz_gate_control(circ, active, |circ, g| {
            for j in 0..w {
                circ.ccx(g, &t[j], &s_rot[j]);
            }
        });
        bit_length_ctz(circ, active, &rev, &t, false, borrowed_carry);
        xor_const(circ, &t, n_pad);
        for q in t {
            circ.zero_and_free(q);
        }
    }

    with_gate_control(circ, active, |circ, g| {
        set_bit_at_s_gated(circ, q_mul, s_rot, g); // q_mul ^= active·(1<<s_rot)
    });

    rotate_left(circ, b, &s_rot[0..rb]); // b <<= s if active (bounded rotator)
    with_gate_control(circ, active, |circ, g| {
        ctrl_add(circ, g, &aref, &bref); // a += b<<s if active
    });

    let pa_hoist = if std::env::var("MIDQ_FUSE_MUL_CLZ").ok().as_deref() == Some("1") {
        without_gate_control(circ, active, |_| {});
        Some(clz_deposit_a(circ, a, w, ca_window))
    } else {
        None
    };

    // o = active AND (bitlen(ca) != bitlen(cb<<s2)) -- ca window, _middle; diff in
    // the clz's pa. This clz is the shrunken_pz_divide_forward peak section.
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| circ.ccx(g, &diff[0], off));
        };
        if let Some(pa) = &pa_hoist {
            if std::env::var("MIDQ_CLZ_OFFSET_PARITY").ok().as_deref() == Some("1") {
                clz_offset_from_hoisted_a(circ, pa, b, ca_window, ca_window, active, off);
            } else {
                clz_diff_use(circ, pa, b, w, ca_window, ca_window, borrowed_carry, use_diff);
            }
        } else {
            clz_diff_body_middle(circ, a, b, w, ca_window, ca_window, borrowed_carry, use_diff);
        }
    });
    rotate_left(circ, b, std::slice::from_ref(off)); // b <<= 1 if o
    ctrl_inc(circ, off, s_rot);
    {
        let lt = circ.alloc_qreg("mg.cleanlt");
        narrow_lt(circ, a, b, &lt, ca_window);
        with_gate_control(circ, active, |circ, g| circ.ccx(g, &lt, off));
        clear_narrow_lt(circ, a, b, &lt, ca_window);
        circ.zero_and_free(lt);
    }
    rotate_right(circ, b, &s_rot[0..rb]); // restore b >>= s_eff (bounded rotator)

    // clean s_rot via _middle clz on (cb, ca): s_rot += (bitlen(cb)-bitlen(ca)).
    without_gate_control(circ, active, |circ| {
        if let Some(pa) = pa_hoist {
            // Reusing pos(a) reverses the difference's sign. Subtraction
            // implements the original s_rot += bitlen(b)-bitlen(a).
            clz_diff_use(circ, &pa, b, w, ca_window, cb_window, borrowed_carry, |circ, diff| {
                let srr: Vec<&QReg> = s_rot.iter().collect();
                let ter: Vec<&QReg> = diff.iter().collect();
                with_peak_gate_control(circ, active, |circ, g| ctrl_sub(circ, g, &srr, &ter));
            });
            clz_undeposit_a(circ, pa, a, ca_window);
        } else {
            clz_diff_body_middle(circ, b, a, w, cb_window, ca_window, borrowed_carry, |circ, diff| {
            let srr: Vec<&QReg> = s_rot.iter().collect();
            let ter: Vec<&QReg> = diff.iter().collect();
            with_peak_gate_control(circ, active, |circ, g| ctrl_add(circ, g, &srr, &ter));
            });
        }
    });
}

/// Gate-by-gate INVERSE of `multiply_substep_windowed` (backward pass). Reverses
/// the sequence; clz/o/q-demux blocks are self-inverse; `rotate_left`<->right,
/// ctrl_add->ctrl_sub, ctrl_inc->ctrl_dec flip. Restores ca -= cb<<s2, re-sets
/// the `q_mul` bit.
#[allow(clippy::too_many_arguments)]
pub fn multiply_substep_windowed_inv(
    circ: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    q_mul: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    active: GateControl<'_>,
    borrowed_carry: Option<&QReg>,
    ca_window: usize,
    cb_window: usize,
    rot_bits: usize,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};
    let aref: Vec<&QReg> = a.iter().collect();
    let bref: Vec<&QReg> = b.iter().collect();
    let n_pad = q_mul.len();
    let rb = rot_bits.min(s_rot.len());
    let w = s_rot.len();
    if std::env::var("MIDQ_RETAIN_MUL_LENGTHS").ok().as_deref() == Some("1") {
        return division_substep_retained_lengths(circ, a, b, q_mul, s_rot,
            off, active, borrowed_carry, ca_window, cb_window, rot_bits, false);
    }
    let pa_hoist = if std::env::var("MIDQ_FUSE_MUL_CLZ").ok().as_deref() == Some("1") {
        without_gate_control(circ, active, |_| {});
        Some(clz_deposit_a(circ, a, w, ca_window))
    } else {
        None
    };

    // 10' s_rot clean inverse: ctrl_add -> ctrl_sub (_middle); diff in the clz's pa.
    without_gate_control(circ, active, |circ| {
        if let Some(pa) = &pa_hoist {
            clz_diff_use(circ, pa, b, w, ca_window, cb_window, borrowed_carry, |circ, diff| {
                let srr: Vec<&QReg> = s_rot.iter().collect();
                let ter: Vec<&QReg> = diff.iter().collect();
                with_peak_gate_control(circ, active, |circ, g| ctrl_add(circ, g, &srr, &ter));
            });
        } else {
            clz_diff_body_middle(circ, b, a, w, cb_window, ca_window, borrowed_carry, |circ, diff| {
            let srr: Vec<&QReg> = s_rot.iter().collect();
            let ter: Vec<&QReg> = diff.iter().collect();
            with_peak_gate_control(circ, active, |circ, g| ctrl_sub(circ, g, &srr, &ter));
            });
        }
    });
    // 9' rotate_left (was rotate_right restore).
    rotate_left(circ, b, &s_rot[0..rb]);
    // 8' clean-o block (self-inverse) -- narrowed, same window as forward.
    {
        let lt = circ.alloc_qreg("mg.cleanlt");
        narrow_lt(circ, a, b, &lt, ca_window);
        with_gate_control(circ, active, |circ, g| circ.ccx(g, &lt, off));
        clear_narrow_lt(circ, a, b, &lt, ca_window);
        circ.zero_and_free(lt);
    }
    // 7' ctrl_inc -> ctrl_dec.
    ctrl_dec(circ, off, s_rot);
    // 6' rotate_right (was rotate_left by o).
    rotate_right(circ, b, std::slice::from_ref(off));
    // 5' o clz block (self-inverse, _middle); diff in the clz's pa.
    without_gate_control(circ, active, |circ| {
        let use_diff = |circ: &mut Circuit, diff: &[QReg]| {
            with_peak_gate_control(circ, active, |circ, g| circ.ccx(g, &diff[0], off));
        };
        if let Some(pa) = pa_hoist {
            if std::env::var("MIDQ_CLZ_OFFSET_PARITY").ok().as_deref() == Some("1") {
                clz_offset_from_hoisted_a(circ, &pa, b, ca_window, ca_window, active, off);
            } else {
                clz_diff_use(circ, &pa, b, w, ca_window, ca_window, borrowed_carry, use_diff);
            }
            clz_undeposit_a(circ, pa, a, ca_window);
        } else {
            clz_diff_body_middle(circ, a, b, w, ca_window, ca_window, borrowed_carry, use_diff);
        }
    });
    // 4' ctrl_add -> ctrl_sub (undo ca += cb<<s2).
    with_gate_control(circ, active, |circ, g| ctrl_sub(circ, g, &aref, &bref));
    // 3' rotate_right (was rotate_left cb<<s2).
    rotate_right(circ, b, &s_rot[0..rb]);
    // 2' q_mul clear demux (self-inverse).
    with_gate_control(circ, active, |circ, g| {
        set_bit_at_s_gated(circ, q_mul, s_rot, g); // q_mul ^= active·(1<<s_rot)
    });
                                                    // 1' s=ctz mask block (self-inverse) -- clears s_rot. Local ctz accumulator.
    {
        let t = circ.alloc_qreg_bits("mg.ctz", w);
        let rev: Vec<&QReg> = q_mul.iter().rev().collect();
        xor_const(circ, &t, n_pad);
        bit_length_ctz(circ, active, &rev, &t, true, borrowed_carry);
        with_ctz_gate_control(circ, active, |circ, g| {
            for j in 0..w {
                circ.ccx(g, &t[j], &s_rot[j]);
            }
        });
        bit_length_ctz(circ, active, &rev, &t, false, borrowed_carry);
        xor_const(circ, &t, n_pad);
        for q in t {
            circ.zero_and_free(q);
        }
    }
}

// NEXT (reversible_pz_notes.md has the primitive mapping):
//   fn normalize_input(circ, x, sgn)               -- x -> min(x,P-x), set sgn
//   fn division_substep(circ, regs, flags, s, bound)
//   fn multiply_substep(circ, regs, flags, s, bound)
//   fn transition(circ, regs, flags)
//   fn iterate(circ, regs, flags, n_iters)         -- the fixed-count driver
//   fn recover_inverse(circ, regs, flags)          -- parity^sgn sign fix
//   test pz_sm_faithful  -- per-iter contract vs a Rust port of pz_big_step

// ===== shrunken_pz reversible inversion step driver (shared fwd/back, used by
// the round-trip test AND the EC-add) =====

// ---- shared forward/backward step helpers (used by the round-trip) ----

/// Like calling `gate_and_active` twice around `body`, but HOLDS the comparator
/// flag `lt=(x<y)` across the substep (which leaves x,y stationary) so the
/// full-width `borrow_compare` runs 2x not 4x. g = (x<y) AND active during body.
pub(crate) fn gate_hold(
    c: &mut Circuit,
    x: &[QReg],
    y: &[QReg],
    active: &QReg,
    g: &QReg,
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    let lt = c.alloc_qreg("gh.lt");
    let xr: Vec<&QReg> = x.iter().collect();
    let yr: Vec<&QReg> = y.iter().collect();
    borrow_compare_refs(c, &xr, &yr, &lt); // lt = (x<y)
    c.ccx(&lt, active, g); // g = lt AND active
    body(c, g);
    c.ccx(&lt, active, g); // uncompute g
    borrow_compare_refs(c, &xr, &yr, &lt); // uncompute lt
    c.zero_and_free(lt);
}

/// Same as `gate_hold`, but folds the step activity predicate into `g` directly
/// instead of holding a separate `active = (counter == 0)` qubit across the body.
pub(crate) fn gate_hold_inline_active(
    c: &mut Circuit,
    x: &[QReg],
    y: &[QReg],
    counter: &[QReg],
    g: &QReg,
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    let lt = c.alloc_qreg("gh.lt");
    let xr: Vec<&QReg> = x.iter().collect();
    let yr: Vec<&QReg> = y.iter().collect();
    borrow_compare_refs(c, &xr, &yr, &lt); // lt = (x<y)
    xor_counter_zero_and_gate(c, counter, &lt, g); // g = lt AND (counter == 0)
    body(c, g);
    xor_counter_zero_and_gate(c, counter, &lt, g); // uncompute g
    borrow_compare_refs(c, &xr, &yr, &lt); // uncompute lt
    c.zero_and_free(lt);
}

/// Same held-comparator schedule as `gate_hold`, but does not materialize
/// `g = lt AND active` across the whole substep. Each active-controlled fragment
/// inside the body computes that AND locally after the clz/bitlength peak has
/// released its prefix scratch.
pub(crate) fn gate_hold_delayed(
    c: &mut Circuit,
    x: &[QReg],
    y: &[QReg],
    active: &QReg,
    body: impl FnOnce(&mut Circuit, GateControl<'_>),
) {
    let lt = c.alloc_qreg("gh.lt");
    let xr: Vec<&QReg> = x.iter().collect();
    let yr: Vec<&QReg> = y.iter().collect();
    borrow_compare_refs(c, &xr, &yr, &lt); // lt = (x<y)
    body(c, GateControl::DelayedAnd { active, gate: &lt });
    borrow_compare_refs(c, &xr, &yr, &lt); // uncompute lt
    c.zero_and_free(lt);
}

/// Hybrid of `gate_hold` and `gate_hold_delayed`: keep the expensive comparator
/// result live, but let the substep drop/rebuild `g = lt AND active` around
/// bitlength peak windows while caching it across the lower-width arithmetic.
pub(crate) fn gate_hold_hybrid(
    c: &mut Circuit,
    x: &[QReg],
    y: &[QReg],
    active: &QReg,
    body: impl FnOnce(&mut Circuit, GateControl<'_>),
) {
    let lt = c.alloc_qreg("gh.lt");
    let xr: Vec<&QReg> = x.iter().collect();
    let yr: Vec<&QReg> = y.iter().collect();
    borrow_compare_refs(c, &xr, &yr, &lt); // lt = (x<y)
    let control = HybridGateControl::new(active, &lt);
    body(c, GateControl::Hybrid(&control));
    control.release(c);
    borrow_compare_refs(c, &xr, &yr, &lt); // uncompute lt
    c.zero_and_free(lt);
}

/// Do not hold the expensive `lt=(x<y)` predicate through bitlength/clz peaks.
/// Instead, recompute `lt` locally at each controlled use. This is value-exact
/// but spends extra compare Toffolis to remove one live predicate qubit from the
/// peak window.
pub(crate) fn gate_hold_recompute_lt(
    c: &mut Circuit,
    x: &[QReg],
    y: &[QReg],
    active: &QReg,
    body: impl FnOnce(&mut Circuit, GateControl<'_>),
) {
    body(c, GateControl::RecomputeLt { x, y, active });
}

/// done-counter (forward: counter += conv) / its inverse (counter -= conv),
/// conv = (A==0 & q==0). `done` is clean scratch (|0> at exit). User's recipe.
pub(crate) fn done_counter_fn(
    c: &mut Circuit,
    aa: &[QReg],
    qq: &[QReg],
    counter: &[QReg],
    inverse: bool,
) {
    if counter.is_empty() {
        return;
    }
    let done = c.alloc_qreg("done");
    let conv = |c: &mut Circuit, done: &QReg| {
        let az = c.alloc_qreg("d.az");
        let qz = c.alloc_qreg("d.qz");
        or_is_zero(c, aa, &az);
        or_is_zero(c, qq, &qz);
        c.ccx(&az, &qz, done); // done ^= (A==0 & q==0)
        clear_zero_predicate(c, qq, &qz, false);
        clear_zero_predicate(c, aa, &az, false);
        c.zero_and_free(qz);
        c.zero_and_free(az);
    };
    let cnz = |c: &mut Circuit, done: &QReg| {
        let z = c.alloc_qreg("d.cnz");
        or_nonzero(c, counter, &z);
        c.cx(&z, done); // done ^= (counter != 0)
        clear_zero_predicate(c, counter, &z, true);
        c.zero_and_free(z);
    };
    if inverse {
        cnz(c, &done);
        ctrl_dec(c, &done, counter);
        conv(c, &done);
    } else {
        conv(c, &done);
        ctrl_inc(c, &done, counter);
        cnz(c, &done);
    }
    c.zero_and_free(done);
}

#[allow(clippy::too_many_arguments)]
fn swap_with_held_predicates(
    c: &mut Circuit,
    aa: &[QReg],
    bb: &[QReg],
    cca: &[QReg],
    ccb: &[QReg],
    parity: &QReg,
    active: &QReg,
    q_zero: &QReg,
    a_nonzero: &QReg,
) {
    let pair = c.alloc_qreg("sw.t");
    let gate = c.alloc_qreg("g_swap");
    c.ccx(q_zero, a_nonzero, &pair);
    c.ccx(&pair, active, &gate);
    for j in 0..aa.len() {
        c.cswap(&gate, &aa[j], &bb[j]);
    }
    for j in 0..cca.len() {
        c.cswap(&gate, &cca[j], &ccb[j]);
    }
    c.cx(&gate, parity);
    c.ccx(&pair, active, &gate);
    c.ccx(q_zero, a_nonzero, &pair);
    c.zero_and_free(gate);
    c.zero_and_free(pair);
}

fn done_counter_from_swap_predicates(
    c: &mut Circuit,
    q_zero: &QReg,
    a_nonzero: &QReg,
    counter: &[QReg],
    inverse: bool,
) {
    if counter.is_empty() {
        return;
    }
    let done = c.alloc_qreg("done");
    c.x(a_nonzero);
    c.ccx(q_zero, a_nonzero, &done);
    if inverse {
        ctrl_dec(c, &done, counter);
    } else {
        ctrl_inc(c, &done, counter);
    }
    // The counter update does not touch the Euclidean state, so the held
    // convergence predicate clears `done` directly and exactly.
    c.ccx(q_zero, a_nonzero, &done);
    c.x(a_nonzero);
    c.zero_and_free(done);
}

#[allow(clippy::too_many_arguments)]
fn swap_and_done_forward(
    c: &mut Circuit,
    aa: &[QReg],
    bb: &[QReg],
    cca: &[QReg],
    ccb: &[QReg],
    qq: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    active: QReg,
) {
    let q_zero = c.alloc_qreg("sw.qz");
    let a_nonzero = c.alloc_qreg("sw.anz");
    or_is_zero(c, qq, &q_zero);
    or_nonzero(c, aa, &a_nonzero);
    swap_with_held_predicates(
        c, aa, bb, cca, ccb, parity, &active, &q_zero, &a_nonzero,
    );

    // The swap preserves q==0 and A!=0 on every reachable PZ state. Reuse
    // those held predicates for the immediately following convergence test.
    uncompute_active(c, counter, &active);
    c.zero_and_free(active);
    done_counter_from_swap_predicates(c, &q_zero, &a_nonzero, counter, false);

    clear_zero_predicate(c, aa, &a_nonzero, true);
    clear_zero_predicate(c, qq, &q_zero, false);
    c.zero_and_free(a_nonzero);
    c.zero_and_free(q_zero);
}

#[allow(clippy::too_many_arguments)]
fn undo_done_and_swap(
    c: &mut Circuit,
    aa: &[QReg],
    bb: &[QReg],
    cca: &[QReg],
    ccb: &[QReg],
    qq: &[QReg],
    counter: &[QReg],
    parity: &QReg,
) -> QReg {
    let q_zero = c.alloc_qreg("sw.qz");
    let a_nonzero = c.alloc_qreg("sw.anz");
    or_is_zero(c, qq, &q_zero);
    or_nonzero(c, aa, &a_nonzero);
    done_counter_from_swap_predicates(c, &q_zero, &a_nonzero, counter, true);

    let active = compute_active(c, counter);
    swap_with_held_predicates(
        c, aa, bb, cca, ccb, parity, &active, &q_zero, &a_nonzero,
    );
    clear_zero_predicate(c, aa, &a_nonzero, true);
    clear_zero_predicate(c, qq, &q_zero, false);
    c.zero_and_free(a_nonzero);
    c.zero_and_free(q_zero);
    active
}

/// One forward (inverse=false) or backward (inverse=true) `shrunken_pz` step on the
/// dynamic-W registers at their current width. Resize is done by the caller.
#[allow(clippy::too_many_arguments)]
pub(crate) fn shrunken_pz_pass_step(
    c: &mut Circuit,
    aa: &[QReg],
    bb: &[QReg],
    cca: &[QReg],
    ccb: &[QReg],
    qq: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    s_rot: &[QReg],
    off: &QReg,
    borrowed_carry: Option<&QReg>,
    i: usize,
    inverse: bool,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{reg_los, shift_bounds};
    fn rb(b: usize) -> usize {
        if b == 0 {
            1
        } else {
            64 - (b as u64).leading_zeros() as usize
        }
    }
    let (lo_a, lo_b, ca_window, cb_window, _) = reg_los(i);
    let (sdb, s2b) = shift_bounds(i);
    let inline_active = lowq_inline_active_enabled();
    let recompute_gate_predicate = lowq_recompute_gate_predicate_enabled();
    let hybrid_gate_hold = lowq_hybrid_gate_hold_enabled();
    let delay_gate_hold = lowq_delay_gate_hold_enabled();
    if inverse {
        let active = undo_done_and_swap(c, aa, bb, cca, ccb, qq, counter, parity);
        if inline_active {
            uncompute_active(c, counter, &active);
            c.zero_and_free(active);

            let g_div = c.alloc_qreg("g_div");
            gate_hold_inline_active(c, cca, ccb, counter, &g_div, |c, g| {
                division_substep_windowed_inv(
                    c,
                    aa,
                    bb,
                    qq,
                    s_rot,
                    off,
                    GateControl::Direct(g),
                    borrowed_carry,
                    lo_a,
                    lo_b,
                    rb(sdb),
                );
            });
            c.zero_and_free(g_div);

            let g_mul = c.alloc_qreg("g_mul");
            gate_hold_inline_active(c, aa, bb, counter, &g_mul, |c, g| {
                multiply_substep_windowed_inv(
                    c,
                    cca,
                    ccb,
                    qq,
                    s_rot,
                    off,
                    GateControl::Direct(g),
                    borrowed_carry,
                    ca_window,
                    cb_window,
                    rb(s2b),
                );
            });
            c.zero_and_free(g_mul);
        } else if recompute_gate_predicate {
            gate_hold_recompute_lt(c, cca, ccb, &active, |c, g| {
                division_substep_windowed_inv(
                    c,
                    aa,
                    bb,
                    qq,
                    s_rot,
                    off,
                    g,
                    borrowed_carry,
                    lo_a,
                    lo_b,
                    rb(sdb),
                );
            });

            gate_hold_recompute_lt(c, aa, bb, &active, |c, g| {
                multiply_substep_windowed_inv(
                    c,
                    cca,
                    ccb,
                    qq,
                    s_rot,
                    off,
                    g,
                    borrowed_carry,
                    ca_window,
                    cb_window,
                    rb(s2b),
                );
            });

            uncompute_active(c, counter, &active);
            c.zero_and_free(active);
        } else if hybrid_gate_hold {
            // Reverse the cross-gated forward schedule. After the forward
            // multiply, ca<cb is the complement of the saved A<B branch bit;
            // division leaves the cofactors stationary.
            let role = c.alloc_qreg("cross.role");
            let car: Vec<&QReg> = cca.iter().collect();
            let cbr: Vec<&QReg> = ccb.iter().collect();
            borrow_compare_refs(c, &car, &cbr, &role);
            let div_control = HybridGateControl::new(&active, &role);
            division_substep_windowed_inv(
                c,
                aa,
                bb,
                qq,
                s_rot,
                off,
                GateControl::Hybrid(&div_control),
                borrowed_carry,
                lo_a,
                lo_b,
                rb(sdb),
            );
            div_control.release(c);

            c.x(&role);
            let mul_control = HybridGateControl::new(&active, &role);
            multiply_substep_windowed_inv(
                c,
                cca,
                ccb,
                qq,
                s_rot,
                off,
                GateControl::Hybrid(&mul_control),
                borrowed_carry,
                ca_window,
                cb_window,
                rb(s2b),
            );
            mul_control.release(c);
            let aar: Vec<&QReg> = aa.iter().collect();
            let bbr: Vec<&QReg> = bb.iter().collect();
            clear_borrow_compare_refs(c, &aar, &bbr, &role);
            c.zero_and_free(role);
            uncompute_active(c, counter, &active);
            c.zero_and_free(active);
        } else if delay_gate_hold {
            gate_hold_delayed(c, cca, ccb, &active, |c, g| {
                division_substep_windowed_inv(
                    c,
                    aa,
                    bb,
                    qq,
                    s_rot,
                    off,
                    g,
                    borrowed_carry,
                    lo_a,
                    lo_b,
                    rb(sdb),
                );
            });

            gate_hold_delayed(c, aa, bb, &active, |c, g| {
                multiply_substep_windowed_inv(
                    c,
                    cca,
                    ccb,
                    qq,
                    s_rot,
                    off,
                    g,
                    borrowed_carry,
                    ca_window,
                    cb_window,
                    rb(s2b),
                );
            });

            uncompute_active(c, counter, &active);
            c.zero_and_free(active);
        } else {
            let g_div = c.alloc_qreg("g_div");
            gate_hold(c, cca, ccb, &active, &g_div, |c, g| {
                division_substep_windowed_inv(
                    c,
                    aa,
                    bb,
                    qq,
                    s_rot,
                    off,
                    GateControl::Direct(g),
                    borrowed_carry,
                    lo_a,
                    lo_b,
                    rb(sdb),
                );
            });
            c.zero_and_free(g_div);

            let g_mul = c.alloc_qreg("g_mul");
            gate_hold(c, aa, bb, &active, &g_mul, |c, g| {
                multiply_substep_windowed_inv(
                    c,
                    cca,
                    ccb,
                    qq,
                    s_rot,
                    off,
                    GateControl::Direct(g),
                    borrowed_carry,
                    ca_window,
                    cb_window,
                    rb(s2b),
                );
            });
            c.zero_and_free(g_mul);

            uncompute_active(c, counter, &active);
            c.zero_and_free(active);
        }
    } else if inline_active {
        let g_mul = c.alloc_qreg("g_mul");
        gate_hold_inline_active(c, aa, bb, counter, &g_mul, |c, g| {
            multiply_substep_windowed(
                c,
                cca,
                ccb,
                qq,
                s_rot,
                off,
                GateControl::Direct(g),
                borrowed_carry,
                ca_window,
                cb_window,
                rb(s2b),
            );
        });
        c.zero_and_free(g_mul);

        let g_div = c.alloc_qreg("g_div");
        gate_hold_inline_active(c, cca, ccb, counter, &g_div, |c, g| {
            division_substep_windowed(
                c,
                aa,
                bb,
                qq,
                s_rot,
                off,
                GateControl::Direct(g),
                borrowed_carry,
                lo_a,
                lo_b,
                rb(sdb),
            );
        });
        c.zero_and_free(g_div);

        let active = compute_active(c, counter);
        swap_and_done_forward(c, aa, bb, cca, ccb, qq, counter, parity, active);
    } else if recompute_gate_predicate {
        let active = compute_active(c, counter);

        gate_hold_recompute_lt(c, aa, bb, &active, |c, g| {
            multiply_substep_windowed(
                c,
                cca,
                ccb,
                qq,
                s_rot,
                off,
                g,
                borrowed_carry,
                ca_window,
                cb_window,
                rb(s2b),
            );
        });

        gate_hold_recompute_lt(c, cca, ccb, &active, |c, g| {
            division_substep_windowed(
                c,
                aa,
                bb,
                qq,
                s_rot,
                off,
                g,
                borrowed_carry,
                lo_a,
                lo_b,
                rb(sdb),
            );
        });

        swap_and_done_forward(c, aa, bb, cca, ccb, qq, counter, parity, active);
    } else if hybrid_gate_hold {
        let active = compute_active(c, counter);
        // Cross-gating invariant: after the multiply substep, ca<cb is exactly
        // the complement of the pre-step A<B bit. One held comparison can
        // therefore select both branches and be cleared from the opposite pair.
        let role = c.alloc_qreg("cross.role");
        let aar: Vec<&QReg> = aa.iter().collect();
        let bbr: Vec<&QReg> = bb.iter().collect();
        borrow_compare_refs(c, &aar, &bbr, &role);
        let mul_control = HybridGateControl::new(&active, &role);
        multiply_substep_windowed(
            c,
            cca,
            ccb,
            qq,
            s_rot,
            off,
            GateControl::Hybrid(&mul_control),
            borrowed_carry,
            ca_window,
            cb_window,
            rb(s2b),
        );
        mul_control.release(c);

        c.x(&role);
        let div_control = HybridGateControl::new(&active, &role);
        division_substep_windowed(
            c,
            aa,
            bb,
            qq,
            s_rot,
            off,
            GateControl::Hybrid(&div_control),
            borrowed_carry,
            lo_a,
            lo_b,
            rb(sdb),
        );
        div_control.release(c);
        let car: Vec<&QReg> = cca.iter().collect();
        let cbr: Vec<&QReg> = ccb.iter().collect();
        clear_borrow_compare_refs(c, &car, &cbr, &role);
        c.zero_and_free(role);

        swap_and_done_forward(c, aa, bb, cca, ccb, qq, counter, parity, active);
    } else if delay_gate_hold {
        let active = compute_active(c, counter);

        gate_hold_delayed(c, aa, bb, &active, |c, g| {
            multiply_substep_windowed(
                c,
                cca,
                ccb,
                qq,
                s_rot,
                off,
                g,
                borrowed_carry,
                ca_window,
                cb_window,
                rb(s2b),
            );
        });

        gate_hold_delayed(c, cca, ccb, &active, |c, g| {
            division_substep_windowed(
                c,
                aa,
                bb,
                qq,
                s_rot,
                off,
                g,
                borrowed_carry,
                lo_a,
                lo_b,
                rb(sdb),
            );
        });

        swap_and_done_forward(c, aa, bb, cca, ccb, qq, counter, parity, active);
    } else {
        let active = compute_active(c, counter);

        let g_mul = c.alloc_qreg("g_mul");
        gate_hold(c, aa, bb, &active, &g_mul, |c, g| {
            multiply_substep_windowed(
                c,
                cca,
                ccb,
                qq,
                s_rot,
                off,
                GateControl::Direct(g),
                borrowed_carry,
                ca_window,
                cb_window,
                rb(s2b),
            );
        });
        c.zero_and_free(g_mul);

        let g_div = c.alloc_qreg("g_div");
        gate_hold(c, cca, ccb, &active, &g_div, |c, g| {
            division_substep_windowed(
                c,
                aa,
                bb,
                qq,
                s_rot,
                off,
                GateControl::Direct(g),
                borrowed_carry,
                lo_a,
                lo_b,
                rb(sdb),
            );
        });
        c.zero_and_free(g_div);

        swap_and_done_forward(c, aa, bb, cca, ccb, qq, counter, parity, active);
    }
}

/// Resize a dynamic-W register to `target` bits: free high qubits (must be |0>)
/// or alloc fresh |0> ones, in place.
pub(crate) fn shrunken_pz_resize(c: &mut Circuit, reg: &mut Vec<QReg>, target: usize, name: &str) {
    while reg.len() > target {
        let q = reg.pop().unwrap();
        c.zero_and_free(q);
    }
    while reg.len() < target {
        let k = reg.len();
        reg.push(c.alloc_qreg(&format!("{name}[{k}]")));
    }
}

/// FORWARD `shrunken_pz` inversion driver. PRE: the registers hold the `S_0` state at width
/// `reg_widths(0)` -- A=p, B=|x| (sign-adjusted, < p/2), ca=0, cb=1, q=0,
/// counter=0, parity=1. Runs all `SHRUNKEN_PZ_NSTEPS` forward steps (resizing per step),
/// leaving the modular inverse of |x| in `ccb` (up to the `parity` bit: the true
/// value is `parity ? cb : p-cb`), with A=p, B=|x| at the EEA terminal. `s`,
/// `s_rot` (9 bits each), `off`, `parity`, `counter` (10 bits) are fixed-width.
#[allow(clippy::too_many_arguments)]
pub(crate) fn shrunken_pz_invert_forward(
    c: &mut Circuit,
    aa: &mut Vec<QReg>,
    bb: &mut Vec<QReg>,
    cca: &mut Vec<QReg>,
    ccb: &mut Vec<QReg>,
    qq: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &QReg,
    s_rot: &mut Vec<QReg>,
    off: &mut Option<QReg>,
    borrowed_carry: Option<&QReg>,
) -> Option<MidqTailState> {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{reg_widths, SHRUNKEN_PZ_NSTEPS};
    let trace_steps = std::env::var_os("MIDQ_TRACE_PZ_STEPS").is_some();
    let mut traced_toffoli = vec![0usize; SHRUNKEN_PZ_NSTEPS];
    let steps = if midq_tail_enabled() { MIDQ_PZ_CUT } else { SHRUNKEN_PZ_NSTEPS };
    for i in 0..steps {
        let trace = trace_steps;
        let start_ops = c.b.current_ops_len();
        let trace_section = trace.then(|| c.push_section(&format!("midq.pz.forward.{i}")));
        let (wa, wb, wca, wcb, wq) = reg_widths(i);
        let wab = trailmix_ab_width(wa.max(wb));
        let wcacb = trailmix_cacb_width(wca.max(wcb));
        shrunken_pz_resize(c, aa, wab, "A");
        shrunken_pz_resize(c, bb, wab, "B");
        shrunken_pz_resize(c, cca, wcacb, "ca");
        shrunken_pz_resize(c, ccb, wcacb, "cb");
        shrunken_pz_resize(c, qq, trailmix_q_width_step(wq, wa, wb, wca, wcb), "q");
        shrunken_pz_pass_step(
            c,
            aa,
            bb,
            cca,
            ccb,
            qq,
            counter,
            parity,
            s_rot,
            off.as_ref().expect("PZ offset scratch is allocated"),
            borrowed_carry,
            i,
            false,
        );
        if let Some(previous) = trace_section {
            c.pop_section(&previous);
            let end_ops = c.b.current_ops_len();
            let toffoli = c.b.ops[start_ops..end_ops]
                .iter()
                .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
                .count();
            traced_toffoli[i] = toffoli;
        }
    }
    if trace_steps {
        for cut in [280usize, 320, 340, 360, 380, 400, 420, 440, 530]
            .into_iter()
            .filter(|&cut| cut <= steps)
        {
            let toffoli: usize = traced_toffoli[..cut].iter().sum();
            eprintln!("MIDQ_PZ_PREFIX forward cut={cut} emitted_toffoli={toffoli}");
        }
    }
    if midq_tail_enabled() {
        if std::env::var("MIDQ_RELEASE_PZ_SCRATCH").ok().as_deref() == Some("1") {
            // A completed PZ step restores these scratch values to zero.
            // Fresh IDs on return let persistent tail values reuse the old IDs.
            for bit in std::mem::take(s_rot) {
                c.zero_and_free(bit);
            }
            c.zero_and_free(off.take().expect("PZ offset scratch"));
        }
        Some(midq_tail_forward(c, aa, bb, cca, ccb, qq, counter, parity))
    } else {
        None
    }
}

/// BACKWARD `shrunken_pz` inversion driver (gate-for-gate inverse of `shrunken_pz_invert_forward`).
/// Restores the `S_0` state (A=p, B=|x|, ca=0, cb=1, q=0, counter=0, parity=1) and
/// uncomputes the inverse from `ccb`. Resizes back down per step.
#[allow(clippy::too_many_arguments)]
pub(crate) fn shrunken_pz_invert_backward(
    c: &mut Circuit,
    aa: &mut Vec<QReg>,
    bb: &mut Vec<QReg>,
    cca: &mut Vec<QReg>,
    ccb: &mut Vec<QReg>,
    qq: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &QReg,
    s_rot: &mut Vec<QReg>,
    off: &mut Option<QReg>,
    borrowed_carry: Option<&QReg>,
    tail_state: Option<MidqTailState>,
) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{reg_widths, SHRUNKEN_PZ_NSTEPS};
    let trace_steps = std::env::var_os("MIDQ_TRACE_PZ_STEPS").is_some();
    let mut traced_toffoli = vec![0usize; SHRUNKEN_PZ_NSTEPS];
    let steps = if tail_state.is_some() { MIDQ_PZ_CUT } else { SHRUNKEN_PZ_NSTEPS };
    if let Some(state) = tail_state {
        midq_tail_backward(c, aa, bb, cca, ccb, qq, counter, parity, state);
        if off.is_none() {
            *s_rot = c.alloc_qreg_bits("midq.restored.srot", trailmix_srot_width());
            *off = Some(c.alloc_qreg("midq.restored.off"));
        }
    }
    for i in (0..steps).rev() {
        let trace = trace_steps;
        let start_ops = c.b.current_ops_len();
        let trace_section = trace.then(|| c.push_section(&format!("midq.pz.backward.{i}")));
        shrunken_pz_pass_step(
            c,
            aa,
            bb,
            cca,
            ccb,
            qq,
            counter,
            parity,
            s_rot,
            off.as_ref().expect("PZ offset scratch is allocated"),
            borrowed_carry,
            i,
            true,
        );
        if let Some(previous) = trace_section {
            c.pop_section(&previous);
            let end_ops = c.b.current_ops_len();
            let toffoli = c.b.ops[start_ops..end_ops]
                .iter()
                .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
                .count();
            traced_toffoli[i] = toffoli;
        }
        if i > 0 {
            let (wa, wb, wca, wcb, wq) = reg_widths(i - 1);
            let wab = trailmix_ab_width(wa.max(wb));
            let wcacb = trailmix_cacb_width(wca.max(wcb));
            shrunken_pz_resize(c, aa, wab, "A");
            shrunken_pz_resize(c, bb, wab, "B");
            shrunken_pz_resize(c, cca, wcacb, "ca");
            shrunken_pz_resize(c, ccb, wcacb, "cb");
            shrunken_pz_resize(c, qq, trailmix_q_width_step(wq, wa, wb, wca, wcb), "q");
        }
    }
    if trace_steps {
        for cut in [280usize, 320, 340, 360, 380, 400, 420, 440, 530]
            .into_iter()
            .filter(|&cut| cut <= steps)
        {
            let toffoli: usize = traced_toffoli[..cut].iter().sum();
            eprintln!("MIDQ_PZ_PREFIX backward cut={cut} emitted_toffoli={toffoli}");
        }
    }
}

const MIDQ_PZ_CUT: usize = 360;
const MIDQ_TAIL_ROUNDS: usize = 224;
#[path = "midq_tail_checkpoint.rs"]
pub(crate) mod midq_tail_checkpoint;
// The 85-bit handoff values have ctz in 0..=85, including the all-zero
// sentinel returned by bit_length_ctz_inplace, so seven bits are exact.
const MIDQ_CTZ_BITS: usize = 7;

// Maximal signed value width at each tail boundary over 200,000 independent
// secp256k1 inputs, widened by one support-tuning bit and made monotone. The
// final floor leaves enough sign extension for the stable signed-unit orbit.
const MIDQ_TAIL_VALUE_WIDTH: [u8; MIDQ_TAIL_ROUNDS + 1] = [
    85,84,83,83,83,83,82,82,82,82,82,81,81,80,80,80,79,79,78,78,78,77,77,77,77,76,75,75,
    75,75,74,74,72,72,72,71,71,71,71,69,69,69,69,69,69,69,68,68,67,66,65,65,65,64,64,64,
    64,63,63,62,62,61,60,60,60,59,59,58,58,57,57,57,57,57,57,56,56,55,55,55,54,54,53,53,
    53,53,53,53,53,53,53,52,52,51,50,50,50,49,49,49,49,49,49,48,48,47,46,46,46,45,45,44,
    44,43,43,41,41,40,40,39,39,39,38,38,37,37,37,36,36,35,34,34,34,33,32,32,32,32,32,31,
    31,30,30,30,30,30,29,29,28,28,28,26,26,26,26,26,26,26,26,25,25,23,23,23,23,22,22,21,
    21,21,20,20,20,20,20,19,19,18,17,17,16,16,16,16,16,16,16,16,16,15,15,15,15,15,15,14,
    14,13,12,11,11,11,10,10,10,10,9,9,9,9,9,8,8,7,7,7,6,6,5,5,4,4,4,4,4,
];

fn midq_tail_enabled() -> bool {
    std::env::var("MIDQ_PZ_PINGPONG_TAIL").ok().as_deref() == Some("1")
}

fn midq_value_vents() -> usize {
    env_usize("MIDQ_VALUE_VENTS", 0)
}

fn midq_toffoli_since(c: &Circuit, start: usize) -> usize {
    c.b.ops[start..]
        .iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

fn midq_signed_resize(c: &mut Circuit, reg: &mut Vec<QReg>, target: usize, name: &str) {
    assert!(target >= 2 && !reg.is_empty());
    while reg.len() > target {
        let high = reg.pop().expect("signed register has a high bit");
        c.cx(reg.last().expect("signed register retains a sign bit"), &high);
        c.zero_and_free(high);
    }
    while reg.len() < target {
        let high = c.alloc_qreg(&format!("{name}.sign[{}]", reg.len()));
        c.cx(reg.last().expect("signed register has a sign bit"), &high);
        reg.push(high);
    }
}

fn midq_flush_quotient(c: &mut Circuit, ca: &[QReg], cb: &[QReg], q: &[QReg], inverse: bool) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};
    assert_eq!(ca.len(), cb.len());
    for (shift, control) in q.iter().enumerate() {
        if shift >= ca.len() {
            break;
        }
        let target: Vec<&QReg> = ca[shift..].iter().collect();
        let source: Vec<&QReg> = cb[..ca.len() - shift].iter().collect();
        if inverse {
            ctrl_sub(c, control, &target, &source);
        } else {
            ctrl_add(c, control, &target, &source);
        }
    }
}

fn midq_compute_ctz(c: &mut Circuit, value: &[QReg], name: &str) -> Vec<QReg> {
    let count = c.alloc_qreg_bits(name, MIDQ_CTZ_BITS);
    xor_const(c, &count, value.len());
    let reversed: Vec<&QReg> = value.iter().rev().collect();
    bit_length_ctz_inplace(c, &reversed, &count, true);
    count
}

fn midq_uncompute_ctz(c: &mut Circuit, value: &[QReg], count: Vec<QReg>) {
    let reversed: Vec<&QReg> = value.iter().rev().collect();
    bit_length_ctz_inplace(c, &reversed, &count, false);
    xor_const(c, &count, value.len());
    for q in count {
        c.zero_and_free(q);
    }
}

fn midq_controlled_swap_registers(
    c: &mut Circuit,
    control: &QReg,
    left: &[QReg],
    right: &[QReg],
) {
    assert_eq!(left.len(), right.len());
    for (a, b) in left.iter().zip(right) {
        c.cswap(control, a, b);
    }
}

fn midq_loan_odd_low_bits(c: &mut Circuit, a: &[QReg], b: &[QReg]) -> [QubitId; 2] {
    let lows = [QubitId(a[0].id().into()), QubitId(b[0].id().into())];
    c.x(&a[0]);
    c.x(&b[0]);
    c.b.free(lows[0]);
    c.b.free(lows[1]);
    lows
}

fn midq_restore_odd_low_bits(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    lows: [QubitId; 2],
) {
    c.b.reacquire(lows[0]);
    c.b.reacquire(lows[1]);
    c.x(&a[0]);
    c.x(&b[0]);
}

fn midq_controlled_shift_right(c: &mut Circuit, control: &QReg, value: &[QReg]) {
    let spill = c.alloc_qreg("midq.cshift.spill");
    for q in value.iter().rev() {
        c.cswap(control, &spill, q);
    }
    c.zero_and_free(spill);
}

fn midq_controlled_shift_right_inverse(c: &mut Circuit, control: &QReg, value: &[QReg]) {
    let spill = c.alloc_qreg("midq.cshift.spill");
    for q in value {
        c.cswap(control, &spill, q);
    }
    c.zero_and_free(spill);
}

fn midq_controlled_mod_halve(c: &mut Circuit, control: &QReg, value: &[QReg], dirty: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;
    assert_eq!(value.len(), 257);
    let parity = c.alloc_qreg("midq.chalve.parity");
    c.ccx(control, &value[0], &parity);
    midq_constant_update(c, &parity, value, &SECP256K1_P_LE, dirty, false);
    midq_controlled_shift_right(c, control, value);
    let measured = c.alloc_bit();
    c.hmr(&parity, measured);
    c.cz_if_bit(control, &value[255], measured);
    c.free_bit(measured);
    c.zero_and_free(parity);
}

fn midq_controlled_mod_halve_inverse(c: &mut Circuit, control: &QReg, value: &[QReg], dirty: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;
    assert_eq!(value.len(), 257);
    let parity = c.alloc_qreg("midq.chalve.parity");
    c.ccx(control, &value[255], &parity);
    midq_controlled_shift_right_inverse(c, control, value);
    midq_constant_update(c, &parity, value, &SECP256K1_P_LE, dirty, true);
    c.ccx(control, &value[0], &parity);
    c.zero_and_free(parity);
}

fn midq_apply_inverse_power_of_two(
    c: &mut Circuit,
    value: &[QReg],
    exponent: &[QReg],
    dirty: &[QReg],
    inverse: bool,
) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    let max_shift = MIDQ_TAIL_VALUE_WIDTH[0] as usize - 1;
    if inverse {
        for shift in (0..max_shift).rev() {
            let control = c.alloc_qreg("midq.shift.active");
            compare_geq_const(c, exponent, &[(shift + 1) as u8], &control);
            midq_controlled_mod_halve_inverse(c, &control, value, dirty);
            compare_geq_const(c, exponent, &[(shift + 1) as u8], &control);
            c.zero_and_free(control);
        }
    } else {
        for shift in 0..max_shift {
            let control = c.alloc_qreg("midq.shift.active");
            compare_geq_const(c, exponent, &[(shift + 1) as u8], &control);
            midq_controlled_mod_halve(c, &control, value, dirty);
            compare_geq_const(c, exponent, &[(shift + 1) as u8], &control);
            c.zero_and_free(control);
        }
    }
}

fn midq_constant_update(
    c: &mut Circuit, control: &QReg, target: &[QReg], value: &[u8],
    dirty: &[QReg], subtract: bool,
) {
    use crate::point_add::trailmix_port::arith::const_add::{
        controlled_add_const, controlled_sub_const,
    };
    use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_add_const_gidney;
    if std::env::var("MIDQ_DIRTY_CONST").ok().as_deref() == Some("1") {
        if subtract { for bit in target { c.x(bit); } }
        controlled_add_const_gidney(c, control, target, value, dirty);
        if subtract { for bit in target { c.x(bit); } }
    } else if subtract {
        controlled_sub_const(c, control, target, value);
    } else {
        controlled_add_const(c, control, target, value);
    }
}

fn midq_field_neg(c: &mut Circuit, control: &QReg, target: &[QReg], dirty: &[QReg]) {
    if std::env::var("MIDQ_DIRTY_FIELD_NEG").ok().as_deref() != Some("1") {
        controlled_field_neg(c, control, target);
        return;
    }
    for bit in target { c.cx(control, bit); }
    midq_constant_update(c, control, target, &p_plus_1_bytes(), dirty, false);
}

fn midq_const_fold(
    c: &mut Circuit,
    target: &[QReg],
    dirty: &[QReg],
    control: &QReg,
    subtract: bool,
) {
    let mut f = [0u8; 32];
    f[0] = 0xd1;
    f[1] = 0x03;
    f[4] = 0x01;
    midq_constant_update(c, control, &target[..256], &f, dirty, subtract);
}

pub(crate) fn midq_dirty_const_selftest() {
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update}, Shake256};
    std::env::set_var("MIDQ_DIRTY_CONST", "1");
    let mut checked = 0usize;
    for n in 2..=6 {
        let mask = (1usize << n) - 1;
        for constant in 0..=mask {
            for subtract in [false, true] {
                let mut circ = Circuit::new();
                let target = circ.alloc_qreg_bits("test.target", n);
                let dirty = circ.alloc_qreg_bits("test.dirty", n-1);
                let ctrl = circ.alloc_qreg("test.ctrl");
                let ids: Vec<_> = target.iter().chain(dirty.iter()).chain([&ctrl])
                    .map(|q| QubitId(q.id().into())).collect();
                midq_constant_update(&mut circ, &ctrl, &target,
                    &[constant as u8], &dirty, subtract);
                let (nq, nb, _, _) = analyze_ops(circ.b.ops.iter());
                let mut seed = Shake256::default();
                seed.update(b"midq-dirty-constant-selftest-v1");
                let mut rng = seed.finalize_xof();
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
                for first in (0..1usize << ids.len()).step_by(64) {
                    sim.clear_for_shot();
                    let valid = 64.min((1usize << ids.len())-first);
                    let active = if valid == 64 {u64::MAX} else {(1u64 << valid)-1};
                    for (index, &id) in ids.iter().enumerate() {
                        for shot in 0..valid {
                            if (first+shot) >> index & 1 == 1 {
                                *sim.qubit_mut(id) |= 1u64 << shot;
                            }
                        }
                    }
                    sim.apply_iter(circ.b.ops.iter());
                    assert_eq!(sim.phase & active, 0, "dirty-adder phase n={n} c={constant}");
                    for shot in 0..valid {
                        let input = first + shot;
                        let old = input & mask;
                        let enabled = input >> (2*n-1) & 1 == 1;
                        let value = if !enabled { old } else if subtract {
                            old.wrapping_sub(constant) & mask
                        } else { (old+constant) & mask };
                        let expected = (input & !mask) | value;
                        for (index, &id) in ids.iter().enumerate() {
                            assert_eq!((sim.qubit(id) >> shot) & 1,
                                ((expected >> index)&1) as u64,
                                "dirty-adder value n={n} c={constant} input={input}");
                        }
                        checked += 1;
                    }
                    for &id in &ids { *sim.qubit_mut(id) = 0; }
                    assert!(sim.qubits.iter().all(|&bits| bits & active == 0), "dirty-adder scratch");
                }
            }
        }
    }
    eprintln!("MIDQ_DIRTY_CONST_SELFTEST PASS: {checked} exhaustive inputs, value/phase/dirty-register restoration");
}

fn midq_signed_mod_add_fast(c: &mut Circuit, sign: &QReg, source: &[QReg], target: &[QReg]) {
    use crate::point_add::trailmix_port::arith::cuccaro::add_cuccaro_with_overflow;
    for q in &target[..256] {
        c.cx(sign, q);
    }
    add_cuccaro_with_overflow(c, target, &source[..256]);

    // In the complemented subtraction frame, the unsigned carry selects the
    // exact pseudo-Mersenne correction +f modulo 2^256.
    midq_const_fold(c, target, source, &target[256], false);
    let lhs: Vec<&QReg> = target[..256].iter().collect();
    let rhs: Vec<&QReg> = source[..256].iter().collect();
    clear_borrow_compare_refs(c, &lhs, &rhs, &target[256]);
    for q in &target[..256] {
        c.cx(sign, q);
    }
}

fn midq_mod_halve_fast(c: &mut Circuit, target: &[QReg], dirty: &[QReg]) {
    let parity = c.alloc_qreg("midq.fast_halve.parity");
    c.cx(&target[0], &parity);
    midq_const_fold(c, target, dirty, &parity, true);
    for i in 0..255 {
        c.b.swap(QubitId(target[i].id().into()), QubitId(target[i + 1].id().into()));
    }
    c.cx(&parity, &target[255]);
    c.cx(&target[255], &parity);
    c.zero_and_free(parity);
}

fn midq_mod_double_fast(c: &mut Circuit, target: &[QReg], dirty: &[QReg]) {
    let overflow = c.alloc_qreg("midq.fast_double.overflow");
    c.b.swap(QubitId(target[255].id().into()), QubitId(overflow.id().into()));
    for i in (0..255).rev() {
        c.b.swap(QubitId(target[i].id().into()), QubitId(target[i + 1].id().into()));
    }
    midq_const_fold(c, target, dirty, &overflow, false);
    c.cx(&target[0], &overflow);
    c.zero_and_free(overflow);
}

fn midq_mod_signed_add_halve(
    c: &mut Circuit,
    target: &[QReg],
    source: &[QReg],
    subtract: &QReg,
    inverse: bool,
) {
    let trace = std::env::var_os("MIDQ_TRACE_CELL").is_some();
    let start = c.b.current_ops_len();
    if inverse {
        midq_mod_double_fast(c, target, source);
        let double_t = midq_toffoli_since(c, start);
        let add_start = c.b.current_ops_len();
        c.x(subtract);
        midq_signed_mod_add_fast(c, subtract, source, target);
        c.x(subtract);
        static BACKWARD: std::sync::OnceLock<()> = std::sync::OnceLock::new();
        if trace && BACKWARD.set(()).is_ok() {
            eprintln!(
                "MIDQ_CELL_BACKWARD total={} double={} add={}",
                midq_toffoli_since(c, start),
                double_t,
                midq_toffoli_since(c, add_start)
            );
        }
    } else {
        midq_signed_mod_add_fast(c, subtract, source, target);
        let add_t = midq_toffoli_since(c, start);
        let halve_start = c.b.current_ops_len();
        midq_mod_halve_fast(c, target, source);
        static FORWARD: std::sync::OnceLock<()> = std::sync::OnceLock::new();
        if trace && FORWARD.set(()).is_ok() {
            eprintln!(
                "MIDQ_CELL_FORWARD total={} add={} halve={}",
                midq_toffoli_since(c, start),
                add_t,
                midq_toffoli_since(c, halve_start)
            );
        }
    }
}

pub(crate) struct MidqTailState {
    tape: Vec<QReg>,
    counter_terminal: Option<QReg>,
    checkpoint: bool,
    quotient_code: Option<Vec<QReg>>,
    ctz: Vec<QReg>,
    ctz_select_a: QReg,
    original_widths: [usize; 4],
}

fn midq_value_round_forward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: &QReg,
    next_width: usize,
) {
    assert_eq!(source.len(), target.len());
    c.cx(&target[1], sign);
    c.cx(&source[1], sign);
    midq_value_round_forward_with_sign(c, source, target, sign, next_width);
}

fn midq_value_round_forward_with_sign(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: &QReg,
    next_width: usize,
) {
    use crate::point_add::trailmix_port::arith::gidney_const_adder::hybrid_add_refs;
    assert_eq!(source.len(), target.len());
    let source_refs: Vec<&QReg> = source.iter().collect();
    let target_refs: Vec<&QReg> = target.iter().collect();
    // sign=0 selects addition. For sign=1, complementing the target around
    // one ordinary add gives ~(~target+source)=target-source modulo 2^w.
    for q in target.iter() {
        c.cx(sign, q);
    }
    hybrid_add_refs(c, &target_refs, &source_refs, midq_value_vents());
    for q in target.iter() {
        c.cx(sign, q);
    }
    let low = target.remove(0);
    c.zero_and_free(low);
    midq_signed_resize(c, target, next_width, "midq.value.target");
    midq_signed_resize(c, source, next_width, "midq.value.source");
}

fn midq_value_round_backward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: QReg,
    old_width: usize,
) {
    use crate::point_add::trailmix_port::arith::gidney_const_adder::hybrid_add_refs;
    midq_signed_resize(c, source, old_width, "midq.value.source");
    midq_signed_resize(c, target, old_width - 1, "midq.value.target");
    target.insert(0, c.alloc_qreg("midq.value.low"));
    let source_refs: Vec<&QReg> = source.iter().collect();
    let target_refs: Vec<&QReg> = target.iter().collect();
    // Undo addition when sign=0 and subtraction when sign=1.
    c.x(&sign);
    for q in target.iter() {
        c.cx(&sign, q);
    }
    hybrid_add_refs(c, &target_refs, &source_refs, midq_value_vents());
    for q in target.iter() {
        c.cx(&sign, q);
    }
    c.x(&sign);
    c.cx(&source[1], &sign);
    c.cx(&target[1], &sign);
    c.zero_and_free(sign);
}

fn midq_tail_forward(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &mut Vec<QReg>,
    cb: &mut Vec<QReg>,
    q: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &QReg,
) -> MidqTailState {
    let trace = std::env::var_os("MIDQ_TRACE_TAIL").is_some();
    let tail_start = c.b.current_ops_len();
    let handoff_section = trace.then(|| c.push_section("midq.tail.forward.handoff"));
    let original_widths = [a.len(), b.len(), ca.len(), cb.len()];
    if trace {
        eprintln!("MIDQ_HANDOFF widths={original_widths:?} q_width={}", q.len());
    }
    shrunken_pz_resize(c, a, MIDQ_TAIL_VALUE_WIDTH[0] as usize, "midq.a");
    shrunken_pz_resize(c, b, MIDQ_TAIL_VALUE_WIDTH[0] as usize, "midq.b");
    shrunken_pz_resize(c, ca, 257, "midq.ca");
    shrunken_pz_resize(c, cb, 257, "midq.cb");

    // At an arbitrary fixed PZ cut, q may still contain the quotient bits
    // already subtracted from a. Applying q*cb to ca restores the adjacent-row
    // invariant while q itself remains available for exact reversal.
    midq_flush_quotient(c, ca, cb, q, false);
    let counter_terminal = counter_tape::enabled().then(|| {
        assert_eq!(counter.len(), counter_tape::BITS, "counter/tape codec requires all eight counter bits");
        counter_tape::prepare(c, a, ca, cb, q)
    });
    let quotient_code = quotient_code::enabled().then(|| quotient_code::compress(c, ca, cb, q));
    if let Some(previous) = handoff_section {
        c.pop_section(&previous);
    }
    let handoff_t = midq_toffoli_since(c, tail_start);

    let normalize_section = trace.then(|| c.push_section("midq.tail.forward.normalize"));
    let ctz = midq_compute_ctz(c, a, "midq.ctz");
    let ctz_b = midq_compute_ctz(c, b, "midq.ctz_b");
    let ctz_select_a = c.alloc_qreg("midq.ctz.select_a");
    c.x(&ctz_select_a);
    c.cx(&a[0], &ctz_select_a);

    // gcd(a,b)=1, so at most one ctz count is nonzero. Encode the pair as
    // k=ctz(a)^ctz(b) plus one bit selecting a; this is a reversible 14-to-8
    // representation on the full reachable Euclidean support.
    for (right, combined) in ctz_b.iter().zip(ctz.iter()) {
        c.cx(right, combined);
    }
    c.x(&ctz_select_a);
    for (combined, right) in ctz.iter().zip(ctz_b.iter()) {
        c.ccx(&ctz_select_a, combined, right);
    }
    c.x(&ctz_select_a);
    for bit in ctz_b {
        c.zero_and_free(bit);
    }

    // Put the only potentially even value in b, strip its power of two once,
    // and restore the original register ordering.
    midq_controlled_swap_registers(c, &ctz_select_a, a, b);
    rotate_right(c, b, &ctz);
    midq_controlled_swap_registers(c, &ctz_select_a, a, b);

    // After quotient flushing, a = (-1)^parity ca*x and
    // b = (-1)^(parity+1) cb*x modulo p. Account for those signs and for
    // the powers of two removed from the positive remainders.
    midq_field_neg(c, parity, ca, cb);
    c.x(parity);
    midq_field_neg(c, parity, cb, ca);
    c.x(parity);
    // Route the matching coefficient through one normalization cell instead
    // of emitting two cells whose controls are mutually exclusive.
    midq_controlled_swap_registers(c, &ctz_select_a, ca, cb);
    midq_apply_inverse_power_of_two(c, cb, &ctz, ca, false);
    midq_controlled_swap_registers(c, &ctz_select_a, ca, cb);
    if let Some(previous) = normalize_section {
        c.pop_section(&previous);
    }
    let normalize_t = midq_toffoli_since(c, tail_start) - handoff_t;

    let checkpoint = midq_tail_checkpoint::enabled();
    let taped_rounds = if checkpoint { midq_tail_checkpoint::START } else { MIDQ_TAIL_ROUNDS };
    let mut tape = Vec::with_capacity(taped_rounds);
    let mut counter_slots = if counter_terminal.is_some() {
        std::mem::take(counter)
    } else {
        Vec::new()
    }.into_iter();
    let mut value_t = 0usize;
    let mut coefficient_t = 0usize;
    for round in 0..taped_rounds {
        let width = MIDQ_TAIL_VALUE_WIDTH[round] as usize;
        let next_width = MIDQ_TAIL_VALUE_WIDTH[round + 1] as usize;
        midq_signed_resize(c, a, width, "midq.a");
        midq_signed_resize(c, b, width, "midq.b");
        let shared = round < counter_tape::BITS && counter_terminal.is_some();
        let sign = if shared {
            counter_slots.next().expect("one counter wire per shared tape slot")
        } else {
            c.alloc_qreg(&format!("midq.sign[{round}]"))
        };
        let decoded = shared.then(|| {
            c.cx(&a[1], &sign);
            c.cx(&b[1], &sign);
            let logical = c.alloc_qreg("midq.counter_tape.decode");
            counter_tape::xor_decoded(c, counter_terminal.as_ref().unwrap(), &sign, &logical);
            logical
        });
        let logical = decoded.as_ref().unwrap_or(&sign);
        let value_start = c.b.current_ops_len();
        let value_section = trace.then(|| c.push_section("midq.tail.forward.value"));
        if round % 2 == 0 {
            if shared {
                midq_value_round_forward_with_sign(c, a, b, logical, next_width);
            } else {
                midq_value_round_forward(c, a, b, logical, next_width);
            }
            if let Some(previous) = value_section {
                c.pop_section(&previous);
            }
            value_t += midq_toffoli_since(c, value_start);
            let coefficient_start = c.b.current_ops_len();
            let coefficient_section =
                trace.then(|| c.push_section("midq.tail.forward.coefficient"));
            let odd_lows = midq_loan_odd_low_bits(c, a, b);
            midq_mod_signed_add_halve(c, cb, ca, logical, false);
            midq_restore_odd_low_bits(c, a, b, odd_lows);
            if let Some(previous) = coefficient_section {
                c.pop_section(&previous);
            }
            coefficient_t += midq_toffoli_since(c, coefficient_start);
        } else {
            if shared {
                midq_value_round_forward_with_sign(c, b, a, logical, next_width);
            } else {
                midq_value_round_forward(c, b, a, logical, next_width);
            }
            if let Some(previous) = value_section {
                c.pop_section(&previous);
            }
            value_t += midq_toffoli_since(c, value_start);
            let coefficient_start = c.b.current_ops_len();
            let coefficient_section =
                trace.then(|| c.push_section("midq.tail.forward.coefficient"));
            let odd_lows = midq_loan_odd_low_bits(c, a, b);
            midq_mod_signed_add_halve(c, ca, cb, logical, false);
            midq_restore_odd_low_bits(c, a, b, odd_lows);
            if let Some(previous) = coefficient_section {
                c.pop_section(&previous);
            }
            coefficient_t += midq_toffoli_since(c, coefficient_start);
        }
        if let Some(logical) = decoded {
            counter_tape::xor_decoded(c, counter_terminal.as_ref().unwrap(), &sign, &logical);
            c.zero_and_free(logical);
        }
        tape.push(sign);
    }
    assert!(counter_slots.next().is_none());

    if checkpoint {
        let start = c.b.current_ops_len();
        let previous = c.push_section("midq.tail.forward.checkpoint");
        midq_tail_checkpoint::forward(c, a, b, ca, cb);
        c.pop_section(&previous);
        coefficient_t += midq_toffoli_since(c, start);
    }

    // At the signed-unit endpoint, the two coefficient rows are respectively
    // u*x^-1 and v*x^-1. Correct the endpoint signs, then clear the duplicate.
    let endpoint_section = trace.then(|| c.push_section("midq.tail.forward.endpoint"));
    let a_sign = if checkpoint { &a[0] } else { a.last().expect("tail a has a sign bit") };
    let b_sign = if checkpoint { &b[0] } else { b.last().expect("tail b has a sign bit") };
    midq_field_neg(c, a_sign, ca, cb);
    midq_field_neg(c, b_sign, cb, ca);
    for (keep, duplicate) in ca.iter().zip(cb.iter()) {
        c.cx(keep, duplicate);
    }
    for wire in std::mem::take(cb) {
        c.zero_and_free(wire);
    }
    if let Some(previous) = endpoint_section {
        c.pop_section(&previous);
    }
    if trace {
        let total = midq_toffoli_since(c, tail_start);
        let endpoint_t = total - handoff_t - normalize_t - value_t - coefficient_t;
        eprintln!(
            "MIDQ_TAIL_FORWARD total={total} handoff={handoff_t} normalize={normalize_t} value={value_t} coefficient={coefficient_t} endpoint={endpoint_t}"
        );
    }

    MidqTailState {
        tape,
        counter_terminal,
        checkpoint,
        quotient_code,
        ctz,
        ctz_select_a,
        original_widths,
    }
}

fn midq_tail_backward(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &mut Vec<QReg>,
    cb: &mut Vec<QReg>,
    q: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &QReg,
    state: MidqTailState,
) {
    let trace = std::env::var_os("MIDQ_TRACE_TAIL").is_some();
    let tail_start = c.b.current_ops_len();
    let MidqTailState {
        mut tape,
        counter_terminal,
        checkpoint,
        quotient_code,
        ctz,
        ctz_select_a,
        original_widths,
    } = state;
    if counter_terminal.is_some() {
        assert!(counter.is_empty(), "shared counter wires belong exclusively to the tape");
    }
    let endpoint_section = trace.then(|| c.push_section("midq.tail.backward.endpoint"));
    *cb = c.alloc_qreg_bits("midq.cb", 257);
    for (keep, duplicate) in ca.iter().zip(cb.iter()) {
        c.cx(keep, duplicate);
    }
    let a_sign = if checkpoint { &a[0] } else { a.last().expect("tail a has a sign bit") };
    let b_sign = if checkpoint { &b[0] } else { b.last().expect("tail b has a sign bit") };
    midq_field_neg(c, b_sign, cb, ca);
    midq_field_neg(c, a_sign, ca, cb);
    if let Some(previous) = endpoint_section {
        c.pop_section(&previous);
    }
    let endpoint_t = midq_toffoli_since(c, tail_start);

    let mut coefficient_t = 0usize;
    let mut value_t = 0usize;
    let taped_rounds = if checkpoint {
        let start = c.b.current_ops_len();
        let previous = c.push_section("midq.tail.backward.checkpoint");
        midq_tail_checkpoint::backward(c, a, b, ca, cb);
        c.pop_section(&previous);
        coefficient_t += midq_toffoli_since(c, start);
        midq_tail_checkpoint::START
    } else {
        MIDQ_TAIL_ROUNDS
    };
    for round in (0..taped_rounds).rev() {
        let sign = tape.pop().expect("one sign per tail round");
        let shared = round < counter_tape::BITS && counter_terminal.is_some();
        let mut encoded = Some(sign);
        let sign = if shared {
            let logical = c.alloc_qreg("midq.counter_tape.decode");
            counter_tape::xor_decoded(c, counter_terminal.as_ref().unwrap(), encoded.as_ref().unwrap(), &logical);
            logical
        } else {
            encoded.take().unwrap()
        };
        let coefficient_start = c.b.current_ops_len();
        let coefficient_section =
            trace.then(|| c.push_section("midq.tail.backward.coefficient"));
        let odd_lows = midq_loan_odd_low_bits(c, a, b);
        if round % 2 == 0 {
            midq_mod_signed_add_halve(c, cb, ca, &sign, true);
            midq_restore_odd_low_bits(c, a, b, odd_lows);
            if let Some(previous) = coefficient_section {
                c.pop_section(&previous);
            }
            coefficient_t += midq_toffoli_since(c, coefficient_start);
            let value_start = c.b.current_ops_len();
            let value_section = trace.then(|| c.push_section("midq.tail.backward.value"));
            midq_value_round_backward(
                c,
                a,
                b,
                sign,
                MIDQ_TAIL_VALUE_WIDTH[round] as usize,
            );
            if let Some(previous) = value_section {
                c.pop_section(&previous);
            }
            value_t += midq_toffoli_since(c, value_start);
        } else {
            midq_mod_signed_add_halve(c, ca, cb, &sign, true);
            midq_restore_odd_low_bits(c, a, b, odd_lows);
            if let Some(previous) = coefficient_section {
                c.pop_section(&previous);
            }
            coefficient_t += midq_toffoli_since(c, coefficient_start);
            let value_start = c.b.current_ops_len();
            let value_section = trace.then(|| c.push_section("midq.tail.backward.value"));
            midq_value_round_backward(
                c,
                b,
                a,
                sign,
                MIDQ_TAIL_VALUE_WIDTH[round] as usize,
            );
            if let Some(previous) = value_section {
                c.pop_section(&previous);
            }
            value_t += midq_toffoli_since(c, value_start);
        }
        if let Some(encoded) = encoded {
            c.cx(&a[1], &encoded);
            c.cx(&b[1], &encoded);
            counter.push(encoded);
        }
    }
    if counter_terminal.is_some() {
        assert_eq!(counter.len(), counter_tape::BITS);
        counter.reverse();
    }
    debug_assert!(tape.is_empty());

    let cleanup_section = trace.then(|| c.push_section("midq.tail.backward.cleanup"));
    midq_controlled_swap_registers(c, &ctz_select_a, ca, cb);
    midq_apply_inverse_power_of_two(c, cb, &ctz, ca, true);
    midq_controlled_swap_registers(c, &ctz_select_a, ca, cb);
    c.x(parity);
    midq_field_neg(c, parity, cb, ca);
    c.x(parity);
    midq_field_neg(c, parity, ca, cb);
    midq_controlled_swap_registers(c, &ctz_select_a, a, b);
    rotate_left(c, b, &ctz);
    midq_controlled_swap_registers(c, &ctz_select_a, a, b);

    // Decode (k, select_a) back into the two ctz registers so their original
    // computations can be reversed against the restored PZ remainders.
    let ctz_b = c.alloc_qreg_bits("midq.ctz_b", MIDQ_CTZ_BITS);
    c.x(&ctz_select_a);
    for (combined, right) in ctz.iter().zip(ctz_b.iter()) {
        c.ccx(&ctz_select_a, combined, right);
    }
    c.x(&ctz_select_a);
    for (right, combined) in ctz_b.iter().zip(ctz.iter()) {
        c.cx(right, combined);
    }
    midq_uncompute_ctz(c, b, ctz_b);
    midq_uncompute_ctz(c, a, ctz);
    c.cx(&a[0], &ctz_select_a);
    c.x(&ctz_select_a);
    c.zero_and_free(ctz_select_a);
    if let Some(code) = quotient_code {
        quotient_code::restore(c, ca, cb, q, code);
    }
    midq_flush_quotient(c, ca, cb, q, true);
    if let Some(terminal) = counter_terminal {
        counter_tape::restore(c, a, ca, cb, q, terminal);
    }

    shrunken_pz_resize(c, a, original_widths[0], "A");
    shrunken_pz_resize(c, b, original_widths[1], "B");
    shrunken_pz_resize(c, ca, original_widths[2], "ca");
    shrunken_pz_resize(c, cb, original_widths[3], "cb");
    if let Some(previous) = cleanup_section {
        c.pop_section(&previous);
    }
    if trace {
        let total = midq_toffoli_since(c, tail_start);
        let cleanup_t = total - endpoint_t - coefficient_t - value_t;
        eprintln!(
            "MIDQ_TAIL_BACKWARD total={total} endpoint={endpoint_t} coefficient={coefficient_t} value={value_t} cleanup={cleanup_t}"
        );
    }
}

/// `lambda = dy / dx mod p`, with `dx` and `dy` PRESERVED. `dx`, `dy` are 257-bit
/// registers holding field elements in [0, p). Returns `(dx, dy, lambda)` -- dx
/// and dy unchanged (dy reconstructed via the HMR-ghost trick), lambda = dy·dx^-1
/// (257 bits, canonical). This is the shrunken_pz-native EC slope: the EEA consumes dx
/// (restored by the reverse), and dy is GHOSTED during the reverse so dy and
/// lambda are never both live across the inversion -> peak ~ EEA-peak + 256.
pub fn shrunken_pz_divide_forward(
    c: &mut Circuit,
    mut dx: Vec<QReg>,
    mut dy: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    use crate::point_add::trailmix_port::arith::rfold_mbu::mod_mul_rfold_mbu;
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    assert_eq!(dx.len(), 257);
    assert_eq!(dy.len(), 257);
    // Field elements are canonical 256-bit values stored in 257 lanes, so lane
    // 256 is a clean passenger. The combined route lends it only across the
    // complete EEA add and returns it before any 257-bit field operation.
    let mut passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("dy has a canonical zero overflow bit"));
    // sgn = dx > p/2  <=>  dx >= (p+1)/2.
    let half_bytes = vec![
        0x18, 0xfe, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x00,
    ];
    let p_bytes = crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    // --- sign-adjust dx -> |dx| < p/2 (the schedule assumes |x| < p/2) ---
    let sgn = c.alloc_qreg("shpzdiv.sgn");
    compare_geq_const(c, &dx, &half_bytes, &sgn);
    controlled_field_neg(c, &sgn, &dx); // dx := (sgn ? p-dx : dx) = |dx|

    // --- set up the inversion S_0 state (B = |dx|, A = p, cb = 1, parity = 1) ---
    let (a0, b0, ca0, cb0, q0) = reg_widths(0);
    let (wg0, wc0) = (a0.max(b0), ca0.max(cb0));
    shrunken_pz_resize(c, &mut dx, wg0, "B"); // |dx| becomes the EEA B register
    let mut aa = c.alloc_qreg_bits("shpzdiv.A", wg0);
    let mut cca = c.alloc_qreg_bits("shpzdiv.ca", wc0);
    let mut ccb = c.alloc_qreg_bits("shpzdiv.cb", wc0);
    let mut qq = c.alloc_qreg_bits("shpzdiv.q", q0.max(1));
    let mut s_rot = c.alloc_qreg_bits("shpzdiv.srot", trailmix_srot_width());
    let mut off = Some(c.alloc_qreg("shpzdiv.off"));
    let parity = c.alloc_qreg("shpzdiv.par");
    let mut counter = c.alloc_qreg_bits("shpzdiv.ctr", trailmix_counter_width());
    let load_p = |c: &mut Circuit, reg: &[QReg]| {
        for (j, q) in reg.iter().enumerate() {
            if j < 256 && (p_bytes[j / 8] >> (j % 8)) & 1 == 1 {
                c.x(q);
            }
        }
    };
    load_p(c, &aa); // A = p
    c.x(&ccb[0]); // cb = 1
    c.x(&parity); // parity = 1

    // --- forward inversion: 1/|dx| in cb (up to the parity bit) ---
    let tail_state = shrunken_pz_invert_forward(
        c,
        &mut aa,
        &mut dx,
        &mut cca,
        &mut ccb,
        &mut qq,
        &mut counter,
        &parity,
        &mut s_rot,
        &mut off,
        passenger_carry.as_ref(),
    );

    if let Some(tail_state) = tail_state {
        // The hybrid tail leaves ca as the canonical inverse of |dx| and
        // retains its compact transcript beside the tail value-state encoding.
        if let Some(carry) = passenger_carry.take() {
            dy.push(carry);
        }
        let mut lambda = c.alloc_qreg_bits("shpzdiv.lambda", 257);
        mod_mul_rfold_mbu(c, &lambda, &cca, &dy);
        midq_field_neg(c, &sgn, &lambda, &cca);

        let mut ghosts = Vec::with_capacity(dy.len());
        for q in &dy {
            ghosts.push(c.hmr_ghost(q));
        }
        for q in dy {
            c.zero_and_free(q);
        }
        passenger_carry = lowq_borrow_passenger_carry_enabled()
            .then(|| lambda.pop().expect("lambda has a canonical zero overflow bit"));

        shrunken_pz_invert_backward(
            c,
            &mut aa,
            &mut dx,
            &mut cca,
            &mut ccb,
            &mut qq,
            &mut counter,
            &parity,
            &mut s_rot,
            &mut off,
            passenger_carry.as_ref(),
            Some(tail_state),
        );

        c.x(&parity);
        c.zero_and_free(parity);
        c.x(&ccb[0]);
        load_p(c, &aa);
        for q in aa.into_iter().chain(cca).chain(ccb).chain(qq) {
            c.zero_and_free(q);
        }
        for q in s_rot.into_iter().chain(counter) {
            c.zero_and_free(q);
        }
        c.zero_and_free(off.take().expect("restored PZ offset scratch"));

        shrunken_pz_resize(c, &mut dx, 257, "dx");
        controlled_field_neg(c, &sgn, &dx);
        compare_geq_const(c, &dx, &half_bytes, &sgn);
        c.zero_and_free(sgn);

        if let Some(carry) = passenger_carry.take() {
            lambda.push(carry);
        }
        let dy_new = c.alloc_qreg_bits("shpzdiv.dy", 257);
        mod_mul_rfold_mbu(c, &dy_new, &lambda[..257], &dx);
        for (g, q) in ghosts.into_iter().zip(dy_new.iter()) {
            c.resolve_ghost(g, q);
        }
        return (dx, dy_new, lambda);
    }

    // --- TEAR DOWN the EEA pack before creating lambda. At convergence the PZ
    // state is A=0, B=1, ca=p, q=0 (all CONSTANTS) and cb=1/|dx| (the only data).
    // Free the constant registers (0-Toffoli uncompute) so only cb is live during
    // the multiply -- saves ~ca(258) qubits at the peak. Re-create them (cheap)
    // before the backward. ---
    let (ta, tb, tca, tq) = (aa.len(), dx.len(), cca.len(), qq.len());
    load_p(c, &cca); // ca: p -> 0
    c.x(&dx[0]); // B: 1 -> 0
    for q in std::mem::take(&mut aa) {
        c.zero_and_free(q); // A = 0
    }
    for q in std::mem::take(&mut dx) {
        c.zero_and_free(q); // B = 0
    }
    for q in std::mem::take(&mut cca) {
        c.zero_and_free(q); // ca = 0
    }
    for q in std::mem::take(&mut qq) {
        c.zero_and_free(q); // q = 0
    }

    // --- lambda = dy * (1/|dx|), parity/sign corrected (only cb live in the pack) ---
    let cb_w = ccb.len();
    shrunken_pz_resize(c, &mut ccb, 257, "cb"); // pad the inverse to 257 for mod_mul
    if let Some(carry) = passenger_carry.take() {
        dy.push(carry);
    }
    let mut lambda = c.alloc_qreg_bits("shpzdiv.lambda", 257);
    mod_mul_rfold_mbu(c, &lambda, &ccb[..257], &dy); // lambda_raw = dy * cb
    shrunken_pz_resize(c, &mut ccb, cb_w, "cb"); // restore width for the backward
                                                 // 1/dx = (-1)^{sgn + (1-parity)} * cb  ->  negate lambda when f = NOT(sgn^par).
    let f = c.alloc_qreg("shpzdiv.negf");
    c.cx(&sgn, &f);
    c.cx(&parity, &f);
    c.x(&f); // f = NOT(sgn XOR parity)
    controlled_field_neg(c, &f, &lambda);
    c.x(&f);
    c.cx(&parity, &f);
    c.cx(&sgn, &f); // uncompute f
    c.zero_and_free(f);

    // --- GHOST dy (HMR each bit, free 256q) so the reverse runs dy-free ---
    let mut ghosts = Vec::with_capacity(dy.len());
    for q in &dy {
        ghosts.push(c.hmr_ghost(q));
    }
    for q in dy {
        c.zero_and_free(q);
    }
    passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| lambda.pop().expect("lambda has a canonical zero overflow bit"));

    // --- RE-CREATE the constant pack (A=0, B=1, ca=p, q=0) for the backward ---
    aa = c.alloc_qreg_bits("shpzdiv.A", ta); // A = 0
    dx = c.alloc_qreg_bits("shpzdiv.B", tb);
    c.x(&dx[0]); // B = 1
    cca = c.alloc_qreg_bits("shpzdiv.ca", tca);
    load_p(c, &cca); // ca = p
    qq = c.alloc_qreg_bits("shpzdiv.q", tq); // q = 0

    // --- backward inversion: restore B = |dx|, uncompute cb/parity ---
    shrunken_pz_invert_backward(
        c,
        &mut aa,
        &mut dx,
        &mut cca,
        &mut ccb,
        &mut qq,
        &mut counter,
        &parity,
        &mut s_rot,
        &mut off,
        passenger_carry.as_ref(),
        None,
    );

    // --- free the clean inversion ancillas (S_0: A=p, ca=0, cb=1, q=0, par=1) ---
    c.x(&parity);
    c.zero_and_free(parity);
    c.x(&ccb[0]); // cb: 1 -> 0
    load_p(c, &aa); // A: p -> 0
    for q in aa.into_iter().chain(cca).chain(ccb).chain(qq) {
        c.zero_and_free(q);
    }
    for q in s_rot.into_iter().chain(counter) {
        c.zero_and_free(q);
    }
    c.zero_and_free(off.take().expect("restored PZ offset scratch"));

    // --- un-sign-adjust: |dx| -> dx, uncompute sgn ---
    shrunken_pz_resize(c, &mut dx, 257, "dx");
    controlled_field_neg(c, &sgn, &dx);
    compare_geq_const(c, &dx, &half_bytes, &sgn);
    c.zero_and_free(sgn);

    // --- reconstruct dy = lambda * dx and EXORCIZE the ghosts ---
    if let Some(carry) = passenger_carry.take() {
        lambda.push(carry);
    }
    let dy_new = c.alloc_qreg_bits("shpzdiv.dy", 257);
    mod_mul_rfold_mbu(c, &dy_new, &lambda[..257], &dx);
    for (g, q) in ghosts.into_iter().zip(dy_new.iter()) {
        c.resolve_ghost(g, q);
    }

    (dx, dy_new, lambda)
}

/// CANCEL the `shrunken_pz` slope: given `lambda` = `new_dy` / `new_dx` (live, 257), drive it to
/// |0> and FREE it, with `new_dx` (dx) and `new_dy` (dy) PRESERVED. Returns
/// (`new_dx`, `new_dy`). By EC linearity `new_dy/new_dx` == lambda, so this is the
/// alt-witness cleanup that removes the slope ancilla after the point coordinates
/// are computed.
///
/// Mirror of `shrunken_pz_divide_forward`, but it GHOSTS lambda (not dy) up front so only
/// `new_dy` rides through the inversion as the passenger (peak = EEA-peak + 256, same
/// as forward). After inverting `new_dx` -> cb = `1/|new_dx`|, it recomputes
/// temp = `new_dy` * cb (parity/sign corrected) = `new_dy/new_dx` == lambda's original
/// value, resolves the lambda-ghost against temp (exorcizing it), uncomputes temp
/// via `mod_mul_rfold_mbu_undo`, then reverse-inverts to restore `new_dx`.
pub fn shrunken_pz_divide_cancel(
    c: &mut Circuit,
    mut dx: Vec<QReg>,
    mut dy: Vec<QReg>,
    lambda: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    use crate::point_add::trailmix_port::arith::rfold_mbu::{mod_mul_rfold_mbu, mod_mul_rfold_mbu_undo};
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    assert_eq!(dx.len(), 257);
    assert_eq!(dy.len(), 257);
    assert_eq!(lambda.len(), 257);
    let mut passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("new_dy has a canonical zero overflow bit"));
    let half_bytes = vec![
        0x18, 0xfe, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x00,
    ];
    let p_bytes = crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    // --- sign-adjust new_dx -> |new_dx| < p/2 ---
    let sgn = c.alloc_qreg("shpzcan.sgn");
    compare_geq_const(c, &dx, &half_bytes, &sgn);
    controlled_field_neg(c, &sgn, &dx);

    // --- GHOST lambda (HMR each bit, free 257q) so the inversion runs lambda-free;
    // new_dy is the sole 256-bit passenger (peak = EEA-peak + 256). ---
    let mut lam_ghosts = Vec::with_capacity(lambda.len());
    for q in &lambda {
        lam_ghosts.push(c.hmr_ghost(q));
    }
    for q in lambda {
        c.zero_and_free(q);
    }

    // --- set up the inversion S_0 (B = |new_dx|, A = p, cb = 1, parity = 1) ---
    let (a0, b0, ca0, cb0, q0) = reg_widths(0);
    let (wg0, wc0) = (a0.max(b0), ca0.max(cb0));
    shrunken_pz_resize(c, &mut dx, wg0, "B");
    let mut aa = c.alloc_qreg_bits("shpzcan.A", wg0);
    let mut cca = c.alloc_qreg_bits("shpzcan.ca", wc0);
    let mut ccb = c.alloc_qreg_bits("shpzcan.cb", wc0);
    let mut qq = c.alloc_qreg_bits("shpzcan.q", q0.max(1));
    let mut s_rot = c.alloc_qreg_bits("shpzcan.srot", trailmix_srot_width());
    let mut off = Some(c.alloc_qreg("shpzcan.off"));
    let parity = c.alloc_qreg("shpzcan.par");
    let mut counter = c.alloc_qreg_bits("shpzcan.ctr", trailmix_counter_width());
    let load_p = |c: &mut Circuit, reg: &[QReg]| {
        for (j, q) in reg.iter().enumerate() {
            if j < 256 && (p_bytes[j / 8] >> (j % 8)) & 1 == 1 {
                c.x(q);
            }
        }
    };
    load_p(c, &aa);
    c.x(&ccb[0]);
    c.x(&parity);

    // --- forward inversion: 1/|new_dx| in cb (passenger: new_dy) ---
    let tail_state = shrunken_pz_invert_forward(
        c,
        &mut aa,
        &mut dx,
        &mut cca,
        &mut ccb,
        &mut qq,
        &mut counter,
        &parity,
        &mut s_rot,
        &mut off,
        passenger_carry.as_ref(),
    );

    if let Some(tail_state) = tail_state {
        if let Some(carry) = passenger_carry.take() {
            dy.push(carry);
        }
        let temp = c.alloc_qreg_bits("shpzcan.temp", 257);
        mod_mul_rfold_mbu(c, &temp, &cca, &dy);
        midq_field_neg(c, &sgn, &temp, &cca);
        for (g, q) in lam_ghosts.into_iter().zip(temp.iter()) {
            c.resolve_ghost(g, q);
        }
        midq_field_neg(c, &sgn, &temp, &cca);
        mod_mul_rfold_mbu_undo(c, &temp, &cca, &dy);
        for q in temp {
            c.zero_and_free(q);
        }
        passenger_carry = lowq_borrow_passenger_carry_enabled()
            .then(|| dy.pop().expect("new_dy has a restored zero overflow bit"));

        shrunken_pz_invert_backward(
            c,
            &mut aa,
            &mut dx,
            &mut cca,
            &mut ccb,
            &mut qq,
            &mut counter,
            &parity,
            &mut s_rot,
            &mut off,
            passenger_carry.as_ref(),
            Some(tail_state),
        );

        c.x(&parity);
        c.zero_and_free(parity);
        c.x(&ccb[0]);
        load_p(c, &aa);
        for q in aa.into_iter().chain(cca).chain(ccb).chain(qq) {
            c.zero_and_free(q);
        }
        for q in s_rot.into_iter().chain(counter) {
            c.zero_and_free(q);
        }
        c.zero_and_free(off.take().expect("restored PZ offset scratch"));

        shrunken_pz_resize(c, &mut dx, 257, "dx");
        controlled_field_neg(c, &sgn, &dx);
        compare_geq_const(c, &dx, &half_bytes, &sgn);
        c.zero_and_free(sgn);
        if let Some(carry) = passenger_carry.take() {
            dy.push(carry);
        }
        return (dx, dy);
    }

    // --- tear down the constant pack (A=0,B=1,ca=p,q=0); keep cb=1/|new_dx| ---
    let (ta, tb, tca, tq) = (aa.len(), dx.len(), cca.len(), qq.len());
    load_p(c, &cca);
    c.x(&dx[0]);
    for q in std::mem::take(&mut aa) {
        c.zero_and_free(q);
    }
    for q in std::mem::take(&mut dx) {
        c.zero_and_free(q);
    }
    for q in std::mem::take(&mut cca) {
        c.zero_and_free(q);
    }
    for q in std::mem::take(&mut qq) {
        c.zero_and_free(q);
    }

    // --- temp = new_dy * (1/|new_dx|), parity/sign corrected = new_dy/new_dx, the
    // original value of lambda. Resolve the lambda-ghost against it, then uncompute
    // temp. ---
    let cb_w = ccb.len();
    shrunken_pz_resize(c, &mut ccb, 257, "cb");
    if let Some(carry) = passenger_carry.take() {
        dy.push(carry);
    }
    let temp = c.alloc_qreg_bits("shpzcan.temp", 257);
    mod_mul_rfold_mbu(c, &temp, &ccb[..257], &dy); // temp_raw = dy * cb
    let f = c.alloc_qreg("shpzcan.negf");
    c.cx(&sgn, &f);
    c.cx(&parity, &f);
    c.x(&f); // f = NOT(sgn XOR parity)
    controlled_field_neg(c, &f, &temp); // temp = +/-(dy*cb) = new_dy/new_dx
    for (g, q) in lam_ghosts.into_iter().zip(temp.iter()) {
        c.resolve_ghost(g, q); // exorcize lambda (temp == lambda's value)
    }
    controlled_field_neg(c, &f, &temp); // un-correct: temp = dy*cb (raw)
    c.x(&f);
    c.cx(&parity, &f);
    c.cx(&sgn, &f); // uncompute f
    c.zero_and_free(f);
    mod_mul_rfold_mbu_undo(c, &temp, &ccb[..257], &dy); // temp -> 0
    for q in temp {
        c.zero_and_free(q);
    }
    shrunken_pz_resize(c, &mut ccb, cb_w, "cb");
    passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("new_dy has a restored zero overflow bit"));

    // --- re-create the pack, backward inversion (restore B=|new_dx|) ---
    aa = c.alloc_qreg_bits("shpzcan.A", ta);
    dx = c.alloc_qreg_bits("shpzcan.B", tb);
    c.x(&dx[0]);
    cca = c.alloc_qreg_bits("shpzcan.ca", tca);
    load_p(c, &cca);
    qq = c.alloc_qreg_bits("shpzcan.q", tq);
    shrunken_pz_invert_backward(
        c,
        &mut aa,
        &mut dx,
        &mut cca,
        &mut ccb,
        &mut qq,
        &mut counter,
        &parity,
        &mut s_rot,
        &mut off,
        passenger_carry.as_ref(),
        None,
    );

    // --- free the clean inversion ancillas (S_0: A=p, ca=0, cb=1, q=0, par=1) ---
    c.x(&parity);
    c.zero_and_free(parity);
    c.x(&ccb[0]);
    load_p(c, &aa);
    for q in aa.into_iter().chain(cca).chain(ccb).chain(qq) {
        c.zero_and_free(q);
    }
    for q in s_rot.into_iter().chain(counter) {
        c.zero_and_free(q);
    }
    c.zero_and_free(off.take().expect("restored PZ offset scratch"));

    // --- un-sign-adjust: |new_dx| -> new_dx, uncompute sgn ---
    shrunken_pz_resize(c, &mut dx, 257, "dx");
    controlled_field_neg(c, &sgn, &dx);
    compare_geq_const(c, &dx, &half_bytes, &sgn);
    c.zero_and_free(sgn);

    if let Some(carry) = passenger_carry.take() {
        dy.push(carry);
    }
    (dx, dy)
}

#[cfg(test)]
mod tests;
