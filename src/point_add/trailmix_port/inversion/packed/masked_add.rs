//! Packed-prefix primitive `masked_add_refs` (`tools/spike/packed_design.md`
//! section 2.3; consumers D7 = the division's field subtract `R1 -= R2` over
//! `[0, E)`, `E = e_B + off`, and M5 = the multiply's field add `R2 += R1` over
//! bits `[0, e_cb)` with the carry captured and absorbed at the toggle leaf).
//!
//! The 3n controlled Cuccaro adder of `arith/cuccaro.rs::controlled_add_cuccaro_3n_refs`
//! (MAJ pass `cx(c,b); cx(c,a); ccx(a,b,c)` = 1 T per cell, UMA pass
//! `ccx(a,b,c); cx(c,a); ccx(ctrl,b,a); cx(c,b)` = 2 T per cell, one carry wire
//! `c` rippling through the whole window) over a classical window of `n` cells
//! (`target[j]`, `addend[j]`, cell 0 = the field's LSB, whatever wires the
//! caller maps them to), where the cells of the *zone* `[zone.start, n)` are
//! masked by a thermometer flag `f_j = [j < E]` for a QUANTUM boundary `E`:
//! the operand bit is replaced by `t = f AND b` (operand-only masking, judge
//! graft G1 of `design_shifted-adders.md` N4):
//!
//! ```text
//!   masked MAJ cell:  ccx(f,c,b); ccx(f,b,t); cx(c,a); ccx(a,t,c); ccx(f,b,t)          4 T
//!   masked UMA cell:  ccx(f,b,t); ccx(a,t,c); cx(c,a); ccx(ctrl,t,a); ccx(f,b,t); ccx(f,c,b)   5 T
//! ```
//!
//! (3 T + 1 T coherent uncompute of `t` / 4 T + 1 T; v1 is fully coherent, no
//! `clear_and`.) With `f = 1` each cell is the plain cell. With `f = 0` the
//! operand contributes nothing, `b` is untouched (every gate on it is gated by
//! `f`), the carry passes through unchanged (`ccx(a,t,c)` with `t = 0`), and the
//! target bit is XORed with the carry-in twice (`cx(c,a)` once per pass):
//! identity. **Foreign TARGET bits above the field end are therefore untouched
//! whatever the carry-in** (they need no gating at all - PFZ's observation);
//! for the plain cells below the zone the same holds under a zero addend bit
//! and a zero carry-in (MAJ/UMA are the identity on `a` then). D7 and M5 rely
//! on exactly this: the target's foreign bits (cb / ca above the field, the gap
//! zeros) are never gated, only the operand's (B / A bits) are masked.
//!
//! Semantics, `E` in `[zone.start, n]` (the support, see below), `ctrl = 1`:
//!
//! ```text
//!   target[0..E) := (target[0..E) + addend[0..E)) mod 2^E          (subtract = false)
//!   target[0..E) := (target[0..E) - addend[0..E)) mod 2^E          (subtract = true: X-bracket
//!                                                                    on the whole target window,
//!                                                                    as ctrl_sub)
//!   c_E := the carry (subtract: the BORROW = [target[0..E) < addend[0..E)]) out of the field
//!   captures.overflow = Some(w):  w ^= c_E            (D4-style capture, "off ^= g_E AND c")
//!   captures.absorb:              target[E] ^= c_E    (M5's absorb into the first wire above
//!                                                      the field: += carry, or -= borrow, i.e.
//!                                                      the (E+1)-bit result when target[E] is
//!                                                      a gap zero)
//!   every other target bit, every addend bit, ctrl, the mask: unchanged
//! ```
//!
//! `ctrl = 0`: nothing changes (the plain cells keep `ctrl`; the one-hot leaves
//! are rooted at `ctrl`, so the captures are gated as well). The design's
//! reverse column ("masked subtract" for M5, "masked add" for D7) is exact: the
//! same call with `subtract` flipped and the same captures is the operator
//! inverse (the twin's captured borrow of `target' - addend` equals the forward
//! carry), and the literal gate-reversed sequence is the inverse as well; the
//! selftest checks both.
//!
//! # The mask
//!
//! * `ZoneMask::Exponent(exp)`: `E` is the value of the little-endian exponent
//!   register `exp` (`e_B` holding `e_B + off` for D7, `e_cb` for M5). The
//!   thermometer is ONE wire `f`, initialised classically to `1 = [zone.start - 1 < E]`
//!   and toggled `f ^= g_i` at every leaf of two one-hot sweeps of
//!   `onehot_stream(c, exp, zone.start, n, Some(ctrl), ..)`: ascending for the
//!   MAJ pass (toggle, then captures, then the cell: at leaf `E` the carry wire
//!   holds the carry out of the field), descending for the UMA pass (the cell,
//!   then the toggle). After the ascending sweep `f = [E >= n]`, which is exactly
//!   the value the descending sweep starts from; after it `f = [E >= zone.start] = 1`
//!   on the support and is X'd away. Wires at the adder moment: `c`, `f`, `t`
//!   (the design's 3) plus the engine's.
//! * `ZoneMask::Sweep(driver)`: any one-hot driver `driver(c, descending, body)`
//!   that calls `body(c, i, g_i)` once per zone cell `i` in the requested order
//!   with `g_i = ctrl AND [i == E]` (asserted: every zone index exactly once, in
//!   order). Same thermometer protocol.
//! * `ZoneMask::Flags(f)`: one caller-owned flag wire per zone cell
//!   (`f[j - zone.start] = [j < E]`, read only). No sweeps, no captures (the
//!   captures need the one-hot leaf; asserted).
//!
//! # Support (preconditions the caller/schedule must guarantee)
//!
//! * `zone.end == n` (the zone is the top of the window, as in D7 and M5); the
//!   plain cells `[0, zone.start)` must lie inside the field, i.e.
//!   **`zone.start <= E`**; `E <= n`. With `E == n` nothing is masked and no
//!   capture fires (the leaf `n` is outside the sweep window `[zone.start, n)`);
//!   `E < zone.start` is a width miss: the thermometer would start at the wrong
//!   value (the toggle leaf is never visited) and every zone cell would add.
//!   For M5 this is `e_cb >= 257 - W_A` (cb's boundary wire at or below `W_A`),
//!   for D7 `e_B + off >= zone.start`: the zone's lower edge must sit at or
//!   below the schedule's lower bound of the exponent (`lo_B`, `lo_cb`), not
//!   only at the envelope intersection.
//!   `E > n` (possible in a 9-bit register) is the same as `E == n`: no leaf
//!   of the sweep window `[zone.start, n)` fires, every cell adds, no capture.
//! * `subtract` without `captures`: the field must not borrow (`A>>s >= B` in
//!   D7), else the low field wraps mod `2^E` (as `ctrl_sub`).
//! * `ctrl` is not a window wire; `exp` / the flags are not window wires.
//!   The `2n` window wires (`target` and `addend`) are pairwise distinct (the
//!   ripple reads `a`, `b` and `c` of one cell as three wires; only `ctrl`
//!   aliasing is asserted, as in `controlled_add_cuccaro_3n_refs`), and the
//!   `captures.overflow` wire is none of the window wires, `ctrl`, `exp` or
//!   the flags (it is the target of `ccx(g_E, c, w)` inside the MAJ sweep;
//!   not asserted).
//!
//! # Cost (Toffoli, coherent v1; measured by the selftest)
//!
//! `3` per plain cell, `9` per zone cell (MAJ 4 + UMA 5; the design's "3 T / 4 T
//! masked cells" plus one coherent `t` uncompute each), `+1` per zone cell per
//! requested capture (`overflow`, `absorb`: one CCX per visited leaf), plus the
//! two engine sweeps (~1 T per visited leaf each with `onehot_stream`'s
//! measured clears, ~2 T coherent). I.e. the design's "8 T extra per zone
//! position against 3 T per plain position" (6 in the cells + 2 engine), 11 T
//! per masked cell in total without captures. The joint capture below shares
//! its product: M5's two target XORs cost one CCX and two CX per leaf, so the
//! combined cost is 12 rather than 13 T per masked cell.
//!
//! # Choices where the design is silent
//!
//! * The thermometer is initialised by a plain `X` (not `cx(ctrl, f)`): on an
//!   inactive row `f = 1` throughout, every zone cell is then the plain cell
//!   whose sum write is gated off by `ctrl`, so the row is exact either way and
//!   the X form needs no gate wire during the setup.
//! * The captures are emitted at the leaf BEFORE the cell (toggle, overflow,
//!   absorb, cell): at that moment `c` is the carry out of cells `[0, i)`; for
//!   the toggle leaf `i = E` that is the field's carry-out. The absorb into
//!   `target[E]` commutes with the masked cell at `E` (which only XORs `c` into
//!   `target[E]` and XORs it back in the UMA pass).
//! * Windows of one cell use the same chain (3 T instead of `cuccaro.rs`'s
//!   1-T special case): never a real case (the windows are 76+ wide) and it
//!   keeps every cell of the same shape.
//! * `n == 0` or an empty zone with `n > 0` are accepted (`zone.start == n`:
//!   the plain 3n adder with a `p.madd` section and no engine sweep).
//!
//! Selftest (`MIDQ_PACKED_SELFTEST=1`, `masked_add_selftest.rs`): widths 1-3
//! and 8 exhaustive over target x addend x boundary x ctrl for every mask
//! kind, subtract and capture setting (width 8: the full matrix at zone edge 3,
//! the edges 0 = all masked and 8 = no zone on the flag and `onehot_stream`
//! kinds), width 9 exhaustive on both sweep engines and width 10 on the
//! reference engine (captures on, both subtract values); widths 11-16
//! exhaustive over boundary x ctrl with random operands; 257 wide (M5's window
//! at steps 378/480: zone edges 181 and 233, plus 0) and 76 wide (D7 at step
//! 378: zone [1, 76)) with random operands, i.e. foreign bits above the
//! boundary in both registers, 9-bit exponents; value, foreign bits, phase 0,
//! every freed ancilla 0, address/flag wires restored, the gate-reversed
//! inverse (coherent kinds) and the X-bracket twin both restore the inputs;
//! T per plain / masked cell, per capture and per engine sweep printed.

use std::ops::Range;

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "masked_add_selftest.rs"]
mod selftest_impl;

/// Where the zone's thermometer `f_j = [j < E]` comes from (module doc).
#[allow(dead_code)]
pub(crate) enum ZoneMask<'a> {
    /// One flag wire per zone cell, `f[j - zone.start] = [j < E]`, read only.
    Flags(&'a [&'a QReg]),
    /// The boundary is the value of this little-endian exponent register; the
    /// one-hot sweeps are `packed::onehot_stream` rooted at `ctrl`.
    Exponent(&'a [QReg]),
    /// The boundary is `register + base` (the 7-bit rebased exponents of
    /// `sched.rs`): the sweeps run over the register values `[zone.start -
    /// base, n - base)`. Requires `zone.start >= base` (a boundary below the
    /// base is unrepresentable, so the cells below it are inside the field
    /// on every representable row and must be plain) and `n - base <= 2^k`.
    Rebased(&'a [QReg], usize),
    /// A caller-supplied one-hot driver: `driver(c, descending, body)` calls
    /// `body(c, i, g_i)` for every zone cell `i` in ascending (`descending =
    /// false`) or descending order with `g_i = ctrl AND [i == E]`.
    Sweep(&'a mut dyn FnMut(&mut Circuit, bool, &mut dyn FnMut(&mut Circuit, usize, &QReg))),
}

/// What to do with the field's carry-out at the toggle leaf `E` (module doc).
#[derive(Clone, Copy, Default)]
#[allow(dead_code)]
pub(crate) struct Captures<'a> {
    /// `w ^= c_E`: the carry (borrow under `subtract`) out of the field.
    pub overflow: Option<&'a QReg>,
    /// `target[E] ^= c_E`: absorb the carry-out into the first wire above the field.
    pub absorb: bool,
}

impl Captures<'_> {
    fn any(&self) -> bool {
        self.overflow.is_some() || self.absorb
    }
}

/// Plain MAJ cell of the 3n controlled Cuccaro (1 T).
#[inline]
fn maj_plain(c: &mut Circuit, carry: &QReg, a: &QReg, b: &QReg) {
    c.cx(carry, b);
    c.cx(carry, a);
    c.ccx(a, b, carry);
}

/// Plain UMA cell of the 3n controlled Cuccaro (2 T).
#[inline]
fn uma_plain(c: &mut Circuit, ctrl: &QReg, carry: &QReg, a: &QReg, b: &QReg) {
    c.ccx(a, b, carry);
    c.cx(carry, a);
    c.ccx(ctrl, b, a);
    c.cx(carry, b);
}

/// Operand-masked MAJ cell: the plain cell with `b` replaced by `t = f AND b` (4 T).
#[inline]
fn maj_masked(c: &mut Circuit, f: &QReg, carry: &QReg, a: &QReg, b: &QReg, t: &QReg, retained: bool) {
    c.ccx(f, carry, b);
    c.ccx(f, b, t);
    c.cx(carry, a);
    c.ccx(a, t, carry);
    if !retained {
        clear_mask_product(c, f, b, t);
    }
}

/// Operand-masked UMA cell (5 T).
#[inline]
fn uma_masked(c: &mut Circuit, f: &QReg, ctrl: &QReg, carry: &QReg, a: &QReg, b: &QReg, t: &QReg, active_mask: bool, retained: bool) {
    if !retained {
        c.ccx(f, b, t);
    }
    c.ccx(a, t, carry);
    c.cx(carry, a);
    if active_mask {
        // t = f*b and f implies ctrl, so ctrl*t = t even on dirty data.
        c.cx(t, a);
    } else {
        c.ccx(ctrl, t, a);
    }
    clear_mask_product(c, f, b, t);
    c.ccx(f, carry, b);
}

fn clear_mask_product(c: &mut Circuit, f: &QReg, b: &QReg, t: &QReg) {
    // f and b have not changed since t = f*b was formed in this cell.
    if std::env::var("MIDQ_MASKED_MEASURED").ok().as_deref() == Some("1") {
        c.clear_and(t, f, b);
    } else {
        c.ccx(f, b, t);
    }
}

fn maj_active(c: &mut Circuit, f: &QReg, carry: &QReg, a: &QReg, b: &QReg, t: &QReg, retained: bool) {
    // maj(a,b,c) = c XOR (a XOR c)(b XOR c). Gate only this last product.
    c.cx(carry, a);
    c.cx(carry, b);
    c.ccx(a, b, t);
    c.ccx(f, t, carry);
    if !retained {
        clear_mask_product(c, a, b, t);
    }
}

fn uma_active(c: &mut Circuit, f: &QReg, carry: &QReg, a: &QReg, b: &QReg, t: &QReg, retained: bool) {
    if !retained {
        c.ccx(a, b, t);
    }
    c.ccx(f, t, carry);
    // a and b still hold their carry-XOR forms at the product's last use.
    clear_mask_product(c, a, b, t);
    c.cx(carry, a);
    c.ccx(f, b, a);
    c.cx(carry, b);
}

pub(super) fn active_mask_enabled() -> bool {
    std::env::var("MIDQ_MASKED_ACTIVE_MASK").ok().as_deref() != Some("0")
}

fn product_cache_len(c: &mut Circuit, cells: usize, address_bits: usize) -> usize {
    if std::env::var("MIDQ_MASKED_PRODUCT_CACHE").ok().as_deref() == Some("0") {
        return 0;
    }
    // Reserve the thermometer and the decoder's endpoint/move peak, not just
    // its leaf workspace. The caller has already allocated carry and shared t.
    let reserve = 1 + super::onehot_stream::gated_scratch(address_bits);
    cells.min(super::sched::scratch_room(c).saturating_sub(reserve))
}

/// The masked 3n controlled Cuccaro adder over refs (module doc).
///
/// `target[j] (+|-)= addend[j]` for the cells `j` below the quantum boundary
/// `E`; the cells of `zone` (`zone.end == target.len()`) are operand-masked by
/// the thermometer of `mask`; `captures` act at the toggle leaf `E`.
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn masked_add_refs(
    c: &mut Circuit,
    ctrl: &QReg,
    target: &[&QReg],
    addend: &[&QReg],
    zone: Range<usize>,
    mut mask: ZoneMask<'_>,
    subtract: bool,
    captures: Captures<'_>,
) {
    let n = target.len();
    assert_eq!(addend.len(), n, "masked_add_refs: target/addend length mismatch");
    assert!(
        zone.start <= zone.end && zone.end == n,
        "masked_add_refs: zone {zone:?} must be the top of the {n}-cell window"
    );
    assert!(
        !target.iter().chain(addend.iter()).any(|q| q.id() == ctrl.id()),
        "masked_add_refs: ctrl aliases a window wire"
    );
    if n == 0 {
        return;
    }
    let z = zone.end - zone.start;
    let prev = c.push_section("p.madd");
    if subtract {
        for q in target {
            c.x(q);
        }
    }
    let carry = c.alloc_qreg("madd.c");
    for i in 0..zone.start {
        maj_plain(c, &carry, target[i], addend[i]);
    }
    if z > 0 {
        let t = c.alloc_qreg("madd.t");
        match &mut mask {
            ZoneMask::Flags(flags) => {
                assert_eq!(flags.len(), z, "masked_add_refs: one flag per zone cell");
                assert!(!captures.any(), "masked_add_refs: captures need a one-hot sweep");
                for i in zone.clone() {
                    maj_masked(c, flags[i - zone.start], &carry, target[i], addend[i], &t, false);
                }
                for i in zone.clone().rev() {
                    uma_masked(c, flags[i - zone.start], ctrl, &carry, target[i], addend[i], &t, false, false);
                }
            }
            ZoneMask::Exponent(exp) => {
                let exp: &[QReg] = *exp;
                let cache_len = product_cache_len(c, z, exp.len());
                let (lo, hi) = (zone.start, zone.end);
                let mut driver = |c: &mut Circuit,
                                  descending: bool,
                                  body: &mut dyn FnMut(&mut Circuit, usize, &QReg)| {
                    super::onehot_stream::onehot_stream(c, exp, lo, hi, Some(ctrl), descending, body);
                };
                masked_sweeps(c, ctrl, target, addend, &zone, &carry, &t, captures, cache_len, &mut driver);
            }
            ZoneMask::Rebased(exp, base) => {
                let exp: &[QReg] = *exp;
                let base = *base;
                let cache_len = product_cache_len(c, z, exp.len());
                assert!(zone.start >= base, "masked_add_refs: zone start {} below the exponent base {base}", zone.start);
                assert!(
                    zone.end - base <= 1usize << exp.len(),
                    "masked_add_refs: window end {} beyond the {}-bit rebased address space at base {base}",
                    zone.end,
                    exp.len()
                );
                let (lo, hi) = (zone.start - base, zone.end - base);
                let mut driver = |c: &mut Circuit,
                                  descending: bool,
                                  body: &mut dyn FnMut(&mut Circuit, usize, &QReg)| {
                    super::onehot_stream::onehot_stream(c, exp, lo, hi, Some(ctrl), descending, &mut |c, i, g| body(c, i + base, g));
                };
                masked_sweeps(c, ctrl, target, addend, &zone, &carry, &t, captures, cache_len, &mut driver);
            }
            ZoneMask::Sweep(driver) => {
                // An arbitrary driver has no known scratch bound.
                masked_sweeps(c, ctrl, target, addend, &zone, &carry, &t, captures, 0, &mut **driver);
            }
        }
        c.zero_and_free(t);
    }
    for i in (0..zone.start).rev() {
        uma_plain(c, ctrl, &carry, target[i], addend[i]);
    }
    c.zero_and_free(carry);
    if subtract {
        for q in target {
            c.x(q);
        }
    }
    c.pop_section(&prev);
}

/// The two one-hot sweeps over the zone with the single-wire thermometer
/// (module doc: ascending MAJ = toggle, captures, cell; descending UMA = cell,
/// toggle). `f` starts and ends at |1> on the support.
#[allow(clippy::too_many_arguments)]
fn masked_sweeps(
    c: &mut Circuit,
    ctrl: &QReg,
    target: &[&QReg],
    addend: &[&QReg],
    zone: &Range<usize>,
    carry: &QReg,
    t: &QReg,
    captures: Captures<'_>,
    cache_len: usize,
    driver: &mut dyn FnMut(&mut Circuit, bool, &mut dyn FnMut(&mut Circuit, usize, &QReg)),
) {
    let f = c.alloc_qreg("madd.f");
    let cache = c.alloc_qreg_bits("madd.product", cache_len);
    let active_mask = active_mask_enabled();
    if active_mask {
        c.cx(ctrl, &f);
    } else {
        c.x(&f);
    }
    let mut next = zone.start;
    driver(c, false, &mut |c, i, g| {
        assert_eq!(i, next, "masked_add_refs: ascending sweep must visit every zone cell in order");
        next += 1;
        c.cx(g, &f); // f = [i < E]
        match (captures.overflow, captures.absorb) {
            (Some(w), true) => {
                // Conjugate the common product fanout; both targets may be dirty.
                c.cx(w, target[i]);
                c.ccx(g, carry, w);
                c.cx(w, target[i]);
            }
            (Some(w), false) => c.ccx(g, carry, w),
            (None, true) => c.ccx(g, carry, target[i]),
            (None, false) => {}
        }
        let saved = cache.get(i - zone.start);
        if active_mask {
            maj_active(c, &f, carry, target[i], addend[i], saved.unwrap_or(t), saved.is_some());
        } else {
            maj_masked(c, &f, carry, target[i], addend[i], saved.unwrap_or(t), saved.is_some());
        }
    });
    assert_eq!(next, zone.end, "masked_add_refs: ascending sweep stopped short");
    driver(c, true, &mut |c, i, g| {
        assert_eq!(next, i + 1, "masked_add_refs: descending sweep must visit every zone cell in order");
        next = i;
        // This cell's transformed operands are unchanged since MAJ.
        let saved = cache.get(i - zone.start);
        if active_mask {
            uma_active(c, &f, carry, target[i], addend[i], saved.unwrap_or(t), saved.is_some());
        } else {
            uma_masked(c, &f, ctrl, carry, target[i], addend[i], saved.unwrap_or(t), false, saved.is_some());
        }
        c.cx(g, &f); // f = [i - 1 < E]
    });
    assert_eq!(next, zone.start, "masked_add_refs: descending sweep stopped short");
    if active_mask {
        c.cx(ctrl, &f);
    } else {
        c.x(&f);
    }
    c.zero_and_free(f);
    for q in cache {
        c.zero_and_free(q);
    }
}

/// Selftest entry called by `packed::selftest_all` (MIDQ_PACKED_SELFTEST=1).
#[allow(dead_code)]
pub(crate) fn selftest() {
    selftest_impl::run();
}
