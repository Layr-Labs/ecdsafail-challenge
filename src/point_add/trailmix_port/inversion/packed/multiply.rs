//! Packed MULTIPLY, forward direction and its exact inverse
//! (`multiply_backward`: the mirrored item order with each item's twin, design
//! 3.4; `packed/inverse.rs` names it `multiply_cancel`) (`tools/spike/packed_design.md` section
//! 3.2, M1-M12 with the 2026-09-13 refuter fixes: M1's two-term `nz` gate, M5's
//! window = the M3 ring with no plain cell below the zone, `e_ca := e_cb + s2 +
//! carry` with the carry captured inside the add). Fires on `gate_mul = active
//! AND role` (the held hybrid gate wire); on `gate_mul = 0` rows every item is
//! the identity on the data (the rotations are ungated permutations by amounts
//! that are 0 or restored, every write is rooted at the gate).
//!
//! State (design section 1): `r1 = [A | gap | cb]`, `r2 = [B | gap | ca]` on two
//! 257-wire rings (values LSB-anchored at wire 0 growing up, coefficient bit `j`
//! at wire `256 - j`); `ex1 = [e_A | e_cb]`, `ex2 = [e_B | e_ca]` (9-bit
//! bit-lengths, LSB first); `q` at its per-step envelope width (LSB-aligned);
//! `s_rot` the 5-bit shift word (0 on entry and exit); `off` the division's
//! offset wire, 0 on entry and exit, used as the multiply's CARRY wire (design
//! 1: "`off` doubles as the multiply's carry wire", so no wire is added at the
//! M5 moment - the reason it is a parameter and not a local).
//!
//! Effect on an active row (`A < B`, `q != 0`, `s2 = ctz(q)`):
//! `ca := ca + (cb << s2)`, `q ^= 1 << s2`, `e_ca := bl(ca_new) = e_cb + s2 +
//! carry`; `A`, `B`, `cb`, `e_A`, `e_B`, `e_cb` untouched; `s_rot`, `off` back
//! to 0; every scratch wire freed at |0>; no phase.
//!
//! The twelve items, each on the primitive it is built from (T = Toffoli at
//! step 378 in the design's table; the measured numbers are printed by the
//! selftest):
//!
//! | # | this file | primitive |
//! |---|---|---|
//! | M1 | `e_ca -= gate * bl(ca_old)` -> 0 (aligned 32-window gap scan on R2, ring `[lo_B, min(257, W_B + 32))`, `nz = [pos != 63] AND [pos < 257 - e_B]`) | `aligned_scan::aligned_scan_bottom` (`lo_B` clamped to 225 by `StepWidths::m1_lo_b`, and 0 on the late rows `lo_B <= 32` so the draining rows' `e_B = 1` is inside the ring) |
//! | M2 | `shift ^= gate * ctz(q)` -> s2 | `ctz::ctz_xor` (direct ctz, chunked to `sched::scratch_room`) |
//! | M3 | rotate the coefficient ring `[256 - W_c, 257)` UP by `s2` (`rb_mul` layers): `ca >> s2` lands on `[257 - e_ca + s2, 257)`, ca's low `s2` bits at the ring bottom | `ring_rotate::ring_rotate` |
//! | M4 | `q ^= gate * (1 << s2)` (clears the bit) | `onehot_stream` on `s_rot` over `[0, min(q.len(), 32))`, leaf `cx(flag, q[i])` |
//! | M5 | `R2 += R1` over cb's field (cells `j = 0..e_cb`, cell `j` = wire `256 - j`), window = the M3 ring (`W_c + 1` cells), zone `[min(257 - W_A, lo_cb + 1), W_c + 1)` masked by the thermometer on `e_cb`; at the toggle leaf `e_cb`: `off ^= carry`, absorb `R2[256 - e_cb] ^= carry` | `masked_add::masked_add_refs` (`ZoneMask::Exponent(e_cb)`, `Captures { overflow: off, absorb }`) |
//! | M6' | `e_ca ^= gate*e_cb; e_ca += gate*shift; e_ca += gate AND off` | `exponent_arith::deposit_sum` |
//! | M8 | `shift += off` -> `D = s2 + carry` | `exponent_arith::ctrl_inc` |
//! | M9 | rotate the ring UP by `off` (1 layer): frame now rotated by `D` | `ring_rotate` |
//! | M10 | `off ^= [(ca_new >> D) < cb]` (clears it): cascade over cells `[cascade_lo, W_c)`, `cascade_lo = max(0, min(lo_ca, lo_cb) - 32)`, capture at leaf `e_cb` | `capture_compare::capture_compare` (`sched.m10_capture_window()`) |
//! | M11 | rotate the ring DOWN by `shift = D` (`rb_mul_plus_carry` layers) | `ring_rotate` |
//! | M12 | `shift ^= gate * (e_ca - e_cb)[0..5]` -> 0 | `exponent_arith::xor_diff_low` |
//!
//! Support (what the schedule guarantees on an active row; a violation is a
//! width / `gap_bound` miss of the support model, never a crash): `e_B in
//! [lo_B + 1, W_B]`; `e_cb in [lo_cb + 1, W_c]`; `bl(ca_new) = e_cb + s2 +
//! carry <= W_c` (so the absorb wire `256 - e_cb - s2` is inside the ring and is
//! a gap zero, or B's MSB with carry provably 0 in the tight case `e_B + s2 +
//! e_cb = 257`); `bl(B) + bl(ca_new) <= 257`; `s2 <= s2_bound` (`rb_mul`
//! layers); the R2 gap `257 - e_B - e_ca <= 31` whenever `ca_old != 0`;
//! `ca_old = 0` rows need nothing of M1's window (the `nz` gate). M10's
//! cascade starts at cell `cascade_lo = max(0, min(lo_ca, lo_cb) - 32)`
//! (review 2026-09-14, finding 7: with the design's `lo_c` bottom the tie of
//! `ca_new >> D` and `cb` on `[lo_c, e_cb)` was a CARRY-ROW-ONLY miss with
//! probability `2^-(e_cb - lo_c)`, certain at `e_cb = lo_c + 1`; 32 more cells
//! make it `<= 2^-33` for `+64` T per multiply row). The q envelope is the real
//! bound on `s2 + carry` (`w_q <= 31`, `sched.rs` "q envelope"; the schedule's
//! `s2_bound` is nominal): `bl(q) > w_q` is the `width_q` miss.
//!
//! Choices where the design is silent (documented here): M4 uses the packed
//! DFS engine (`onehot_stream`) instead of `set_bit_at_s_gated`'s measured
//! demux - identical tree, identical T (~1 per q bit), no env switch; the
//! ctz kernel is a local twin of `direct_ctz::emit` (private there) planned
//! against `MIDQ_PACKED_QCAP` (866) - `MIDQ_PACKED_CTZ_ROOM` pins the room;
//! the M5 zone edge folds the schedule's `lo_cb` in (the `masked_add` support
//! note: the plain cells must lie inside cb's field on EVERY support row, and
//! `257 - W_A` alone does not guarantee that - at step 378 of the static table
//! it is 174 against `lo_cb + 1 = 173`); M11's layer count is that of
//! `s2_bound + 1` (D may cross a power of two); M1's `lo_B` is clamped to 225
//! so the window never passes wire 257 (steps 0-2 of the static table have
//! `B_LO = 226-227`; B's low bits then wrap into the window, the refuter-2
//! case the `nz` gate covers).
//!
//! Environment: inherits `aligned_scan_bottom`'s `MIDQ_KG_ZERO_LAYER=1` and
//! `MIDQ_CHUNKED_PREFIX != 1` (asserted there); `MIDQ_ONEHOT_COHERENT=1` makes
//! every engine clear coherent (debug).
//!
//! Selftest (`MIDQ_PACKED_SELFTEST=1`, `multiply_selftest.rs`): >= 64 model
//! inputs x every multiply row up to 530 against the exact `pz_prefix`
//! recurrence, plus synthetic rows for the required classes; forward on the
//! real states, `gate = 0` rows, phase 0, ancillae clean; T at 100 / 250 / 378.

use super::aligned_scan::aligned_scan_bottom;
use super::capture_compare::capture_compare;
use super::ctz::ctz_xor;
use super::exponent_arith::{ctrl_dec, ctrl_inc, deposit_sum, undeposit_sum, xor_diff_low};
use super::masked_add::{masked_add_refs, Captures, ZoneMask};
use super::onehot_stream::onehot_stream;
use super::ring_rotate::ring_rotate;
use super::sched::{scratch_room, StepWidths, EXP_BITS, RING};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "multiply_selftest.rs"]
mod selftest_impl;

/// The packed multiply, forward direction (module doc). `ex1 = [e_A | e_cb]`,
/// `ex2 = [e_B | e_ca]`; `off` is the shared carry wire (0 on entry/exit);
/// `gate_mul` the held `active AND role`; `sched` the step's envelope.
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn multiply_forward(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
) {
    multiply_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_mul, step, sched, false, &mut |_, _| {});
}

/// The exact inverse of [`multiply_forward`] (the backward driver's multiply,
/// design 3.4): the mirrored item order M12, M11, M10, M9, M8, M6', M5, M4,
/// M3, M2, M1 with every item's twin (self-inverse items unchanged, rotations
/// reversed, `deposit_sum` -> `undeposit_sum`, `ctrl_inc` -> `ctrl_dec`, the
/// masked add -> the masked subtract with the same captures, the scan with
/// `inverse = true`). PRE: the forward's POST state (`s_rot = 0`, `off = 0`,
/// LSB frame). On a `gate_mul = 1` row: `ca := ca - (cb << s2)` with `s2` read
/// off `e_ca - e_cb` and the captured carry, `q ^= 1 << s2`, `e_ca := bl(ca_old)`.
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn multiply_backward(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
) {
    multiply_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_mul, step, sched, true, &mut |_, _| {});
}

/// [`multiply_forward`] with an item marker: `mark(c, name)` is called at the
/// start of every item (`"M1"` .. `"M12"`) and once at the end (`"end"`), so a
/// harness can attribute `c.b.ops` ranges to items (the selftest's per-item T).
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn multiply_forward_marked(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
    mark: &mut dyn FnMut(&Circuit, &'static str),
) {
    multiply_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_mul, step, sched, false, mark);
}

/// [`multiply_backward`] with the item marker (items arrive in the mirrored order).
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn multiply_backward_marked(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
    mark: &mut dyn FnMut(&Circuit, &'static str),
) {
    multiply_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_mul, step, sched, true, mark);
}

/// One definition of the twelve items; `inverse` selects the twin of each and
/// the mirrored order (the forward gate stream is unchanged by this sharing).
#[allow(clippy::too_many_arguments)]
fn multiply_step(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
    inverse: bool,
    mark: &mut dyn FnMut(&Circuit, &'static str),
) {
    let who = if inverse { "multiply_backward" } else { "multiply_forward" };
    assert_eq!(r1.len(), RING, "{who}: R1 must be the 257-wire ring");
    assert_eq!(r2.len(), RING, "{who}: R2 must be the 257-wire ring");
    assert_eq!(ex1.len(), 2 * EXP_BITS, "{who}: ex1 = [e_A | e_cb]");
    assert_eq!(ex2.len(), 2 * EXP_BITS, "{who}: ex2 = [e_B | e_ca]");
    assert!(!s_rot.is_empty(), "{who}: empty shift word");
    assert_eq!(sched.step, step, "{who}: schedule row mismatch");
    let e_cb = &ex1[EXP_BITS..];
    let e_b = &ex2[..EXP_BITS];
    let e_ca = &ex2[EXP_BITS..];
    // The rebased frame (sched.rs): e_B holds `e_B - base_v`, e_ca / e_cb hold
    // `e - base_c`; M1's scan and M5's mask take the bases, M6'/M12 are
    // base-free (same base on both operands, arithmetic mod 2^7).
    let (base_v, base_c) = (sched.base_v(), sched.base_c());
    let ring = &r2[sched.coef_ring()];
    let rb = sched.rb_mul.min(s_rot.len());
    let rb2 = sched.rb_mul_plus_carry().min(s_rot.len());
    let n = sched.mul_window_cells();
    let sec = c.push_section(if inverse { "pk.mul.inv" } else { "pk.mul" });

    // ---- items as closures so the two directions share one definition ----
    // M1: e_ca -> 0 by the aligned gap scan (LSB frame, R2 unrotated); inverse: += bl(ca_old).
    let m1 = |c: &mut Circuit, inv: bool| {
        aligned_scan_bottom(c, r2, e_b, e_ca, gate_mul, sched.w_b, sched.m1_lo_b(), base_v, base_c, inv);
    };
    // M2: shift ^= gate * ctz(q) (self-inverse).
    let m2 = |c: &mut Circuit| {
        let room = scratch_room(c);
        ctz_xor(c, q, s_rot, gate_mul, room);
    };
    // M3: coefficient ring UP by s2 (inverse: down).
    let m3 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, &s_rot[..rb], inv);
    // M4: q ^= gate * (1 << s2) (self-inverse).
    let m4 = |c: &mut Circuit| {
        let hi = q.len().min(1usize << s_rot.len());
        onehot_stream(c, s_rot, 0, hi, Some(gate_mul), false, &mut |c, i, flag| {
            c.cx(flag, &q[i]);
        });
    };
    // M5: R2 += R1 over cb's field, carry captured into `off` and absorbed
    // (inverse: the masked subtract with the same captures).
    let m5 = |c: &mut Circuit, inv: bool| {
        let target: Vec<&QReg> = (0..n).map(|j| &r2[RING - 1 - j]).collect();
        let addend: Vec<&QReg> = (0..n).map(|j| &r1[RING - 1 - j]).collect();
        masked_add_refs(
            c,
            gate_mul,
            &target,
            &addend,
            sched.mul_zone_start()..n,
            ZoneMask::Rebased(e_cb, base_c),
            inv,
            Captures { overflow: Some(off), absorb: true },
        );
    };
    // M6': e_ca := e_cb + s2 + carry (inverse: -> 0).
    let m6 = |c: &mut Circuit, inv: bool| {
        if inv {
            undeposit_sum(c, gate_mul, e_ca, e_cb, s_rot, off);
        } else {
            deposit_sum(c, gate_mul, e_ca, e_cb, s_rot, off);
        }
    };
    // M8: shift += carry -> D (inverse: -= carry).
    let m8 = |c: &mut Circuit, inv: bool| {
        if inv {
            ctrl_dec(c, off, s_rot);
        } else {
            ctrl_inc(c, off, s_rot);
        }
    };
    // M9: ring UP by carry (inverse: down).
    let m9 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, std::slice::from_ref(off), inv);
    // M10: off ^= [(ca_new >> D) < cb], capture at leaf e_cb (self-inverse).
    let m10 = |c: &mut Circuit| {
        let lo_c = sched.m10_cascade_lo();
        let v: Vec<&QReg> = (lo_c..sched.w_c).map(|j| &r2[RING - 1 - j]).collect();
        let u: Vec<&QReg> = (lo_c..sched.w_c).map(|j| &r1[RING - 1 - j]).collect();
        capture_compare(c, gate_mul, &v, &u, e_cb, sched.m10_capture_window(), off);
    };
    // M11: ring DOWN by shift = D (inverse: up).
    let m11 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, &s_rot[..rb2], !inv);
    // M12: shift ^= gate * (e_ca - e_cb) (self-inverse).
    let m12 = |c: &mut Circuit| xor_diff_low(c, gate_mul, e_ca, e_cb, s_rot);

    fn item(
        c: &mut Circuit,
        mark: &mut dyn FnMut(&Circuit, &'static str),
        name: &'static str,
        body: impl FnOnce(&mut Circuit),
    ) {
        mark(c, name);
        let s = c.push_section(name);
        body(c);
        c.pop_section(&s);
    }
    if !inverse {
        item(c, mark, "M1", |c| m1(c, false));
        item(c, mark, "M2", |c| m2(c));
        item(c, mark, "M3", |c| m3(c, false));
        item(c, mark, "M4", |c| m4(c));
        item(c, mark, "M5", |c| m5(c, false));
        item(c, mark, "M6", |c| m6(c, false));
        item(c, mark, "M8", |c| m8(c, false));
        item(c, mark, "M9", |c| m9(c, false));
        item(c, mark, "M10", |c| m10(c));
        item(c, mark, "M11", |c| m11(c, false));
        item(c, mark, "M12", |c| m12(c));
    } else {
        item(c, mark, "M12", |c| m12(c));
        item(c, mark, "M11", |c| m11(c, true));
        item(c, mark, "M10", |c| m10(c));
        item(c, mark, "M9", |c| m9(c, true));
        item(c, mark, "M8", |c| m8(c, true));
        item(c, mark, "M6", |c| m6(c, true));
        item(c, mark, "M5", |c| m5(c, true));
        item(c, mark, "M4", |c| m4(c));
        item(c, mark, "M3", |c| m3(c, true));
        item(c, mark, "M2", |c| m2(c));
        item(c, mark, "M1", |c| m1(c, true));
    }
    mark(c, "end");
    c.pop_section(&sec);
}

/// Selftest entry called by `packed::selftest_all` (`MIDQ_PACKED_SELFTEST=1`).
#[allow(dead_code)]
pub(crate) fn selftest() {
    selftest_impl::run();
}
