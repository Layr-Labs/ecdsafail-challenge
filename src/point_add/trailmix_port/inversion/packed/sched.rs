//! Per-step envelope of one packed prefix step (`tools/spike/packed_design.md`
//! sections 1, 3): the numbers the division (D0-D12), the multiply (M1-M12)
//! and the role/swap code read off the schedule, in ONE struct so that every
//! ring, window, zone and layer count has a single definition (Phase 2 review,
//! 2026-09-14: the division used to carry its own `StepWidths` with a second
//! `lo_b` source; both are gone).
//!
//! Sources (`shrunken_pz_schedule.rs`): `reg_widths(i)` = the per-step maxima
//! `(A, B, ca, cb, q)` (`record_sample` :442-506, incl. the old circuit's
//! `B << s` / `cb << s2` transients, so they are conservative for the packed
//! rings), `shift_bounds(i)` = the division / multiply shift ceilings, turned
//! into rotation layer counts exactly as `shrunken_pz_pass_step` does (`rb(b)` =
//! bit-length of the bound, 1 for a 0 bound), and **`thin_lo(width)`** for every
//! `lo`: the MSB of register X lies in its top `thin_clz_window()` wires
//! (`TRAILMIX_THIN_CLZ_WINDOW`, 78 on the route), i.e. `e_X >= lo_X + 1` on the
//! support. Under the production thin schedule this IS `reg_los` (giveback 0);
//! under the static tables it replaces their own `*_LO` columns (the old
//! circuit's clz-window bounds, e.g. `B_LO = 227` at step 0 against
//! `thin_lo(256) = 178`), so both schedules give the packed circuit one
//! convention and the support model has one formula to mirror. (The static
//! tables are not a valid packed schedule anyway: their q envelope reaches 38,
//! see "q envelope" below.)
//!
//! Derived geometry (all `usize`, wire indices on the 257-wire rings):
//!
//! * `w_a = max(A, B)`: the value ring is `[0, w_a)` (D3/D5/D10, D4/D9's
//!   cascade top); `w_b` = B's own envelope (M1's ring top `min(257, w_b + 32)`);
//! * `w_c = max(ca, cb)`: the coefficient ring is `[256 - w_c, 257)` (M3/M9/M11;
//!   M5's window = the ring, `w_c + 1` cells; M10's cascade top);
//! * `lo_*`: `thin_lo` of each envelope (`e_X >= lo_X + 1`);
//! * `rb_div`, `rb_mul`: rotation layers for `s` (D3/D10) and `s2` (M3);
//!   [`StepWidths::rb_mul_plus_carry`] for M11's amount `s2 + carry`.
//!
//! # Division geometry (design 3.1 with the review fixes)
//!
//! * [`StepWidths::div_cascade_lo`] - the D4/D9 cascade bottom. The design's
//!   cascade started at `lo_b` (both operands end at `e_B`), which made the
//!   window-tie residue `P = 2^-(e_B - lo_b - 1)` per row: with `e_B = lo_b + 1`
//!   rows common at the widest steps it was the DOMINANT miss kind (0.12% of
//!   inputs in the 8k pool, more than every width kind together). The cascade
//!   now starts 32 cells lower, `max(0, lo_b - 32)`, so the residue is
//!   `<= 2^-32` per row (`+2 x 32` T per compare; 0 when `lo_b <= 32`, where
//!   the cascade starts at wire 0 and there is no residue at all).
//! * [`StepWidths::div_capture_window`] - the D4/D9 address window: `e_B` in
//!   `[lo_b + 1, w_a]` while `lo_b > 32` (rows below `lo_b + 1` are D7/D11
//!   misses anyway), and `[1, w_a]` once `lo_b <= 32` (every `e_B >= 1`
//!   captures; together with the zone below and [`StepWidths::lo_b_free`],
//!   the step then has NO `lo_b` dependence on the late rows, so
//!   fast-converging inputs stop being misses).
//! * [`StepWidths::div_zone_start`] - D7's masked zone `[start, w_a)`. The
//!   masked adder's thermometer starts at 1, so `start <= E = e_B + off` is a
//!   precondition on every active row: a row with `E < start` never visits its
//!   toggle leaf, every window cell stays plain and ca's bits inside `[E, w_a)`
//!   are subtracted into R1 (a certain failure, not a residue). Plain cells
//!   below `257 - w_c` can never see a ca bit, and plain cells below `lo_b + 1`
//!   are inside the field on the support, so `start = min(257 - w_c, lo_b + 1)`
//!   on the mid rows (empty zone when `257 - w_c >= w_a`) and `start = 1` on
//!   the late rows (`lo_b <= 32`): D7 is then exact for every `e_B >= 1`. The
//!   design's `max(lo_a, 257 - w_c)` clamp is gone (it made every B = 1 row
//!   with `e_B <= lo_b` and a wide ca a certain failure); the late-row zone
//!   costs `+8` T per cell in `[1, min(257 - w_c, lo_b + 1))`, i.e. `+296` T
//!   at step 310, `+168` at 340, 0 from 371.
//! * [`StepWidths::div_term_window`] - D0's OR-capture window `min(28, w_a)`
//!   (a terminal division with `s > 28` is the `term_window` miss; measured
//!   terminal `s <= 9` over 160k inputs).
//! * [`StepWidths::div_scan_window`] - D11's window width (`aligned_scan`).
//!
//! # Multiply geometry
//!
//! * [`StepWidths::mul_zone_start`] - M5's zone edge `min(257 - w_a, lo_cb + 1)`
//!   (design erratum, review 2026-09-14: the design's `z_c = W_A + W_c - 256`
//!   alone leaves the toggle leaf `e_cb` outside the sweep on every early
//!   multiply with `e_cb < 257 - W_A`, and A's bits are added into R2; the
//!   `lo_cb + 1` clamp is load-bearing - a mutation test fails at step 1).
//! * [`StepWidths::m1_lo_b`] - M1's ring bottom: `lo_b` clamped so the
//!   32-window stays below wire 257, and 0 on the late rows (`lo_b <= 32`,
//!   [`StepWidths::lo_b_free`]): the draining rows (B = 1) of an input frozen
//!   before `lo_b` reaches 0 need `e_B = 1 >= lo_b` for the rotation amount
//!   `e_B - lo_b` (`+14 lo_b` T per multiply row there).
//! * [`StepWidths::m10_lo_c`] / [`StepWidths::m10_cascade_lo`] - M10's address
//!   window bottom and its cascade bottom: the window-tie residue of M10 is a
//!   carry-row-only miss with `P = 2^-(e_cb - cascade_lo)`; the cascade starts
//!   32 cells below `min(lo_ca, lo_cb)` so it is `<= 2^-33` (`+64` T per
//!   multiply row).
//!
//! # q envelope (review finding 6)
//!
//! `s2_bound` from `shift_bounds` is nominal (31 / 63 in the static tables;
//! `rot_layers` clamps to the 5-bit shift word), so it does NOT bound
//! `D = s2 + carry`. The real guard is the q envelope: `bl(q) <= w_q` on the
//! support (the `width_q` miss kind) with **`w_q <= 31`**, which gives
//! `s2 <= 30` and `D <= 31` (fits the 5-bit word) and `q.len() <= 32` for D8's
//! demux and D12's gray deposit. The driver asserts `w_q <= 31` per step
//! ([`StepWidths::assert_packed_step`]); the thin schedule's maximum is 29.
//! The support model must state `bl(q) <= min(w_q, 31)` explicitly.
//!
//! Scratch budget: [`scratch_room`] gives the number of wires a substep may
//! allocate at the current moment without exceeding the packed peak
//! (`MIDQ_PACKED_QCAP`, default 850: the 7-bit rebased exponents and the q
//! clamp at 22 under design section 5's 866 accounting); the direct-ctz
//! kernel (`packed::ctz`) is the one consumer that plans against it
//! (`MIDQ_PACKED_CTZ_ROOM` overrides the room directly, for measurement).

#![allow(dead_code)]

use super::capture_compare::{CaptureWindow, FieldEnd};
use crate::point_add::trailmix_port::circuit::Circuit;
use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{packed_q_width, reg_widths, shift_bounds, thin_lo};

/// The 257-wire rings.
pub(crate) const RING: usize = 257;
/// Exponent register width: the 7-bit REBASED exponents of design section 8
/// (lever G4). Each register holds `e_X - base(step)` mod 2^7 where the base
/// is shared by the two exponents of a ring pair (`e_A`/`e_B`: [`exp_base`] of
/// `w_a`; `e_ca`/`e_cb`: [`exp_base`] of `w_c`), so the role swap stays a plain
/// cswap and the per-step rebase is one unconditional `add_const` per
/// register (`p0_shape::rebase_exponents`). See [`StepWidths::base_v`].
pub(crate) const EXP_BITS: usize = 7;
/// Number of values a rebased register holds.
pub(crate) const EXP_SPAN: usize = 1 << EXP_BITS;

/// The rebase of a ring pair whose envelope (ring top) is `w`: the register
/// range `[base, base + 127]` is the widest window that still contains the
/// ring top, so every exponent in `[w - 127, w]` is representable. On the
/// support `e_X <= w` (width) and `max(e_X, e_Y) >= w - 77` (the thin clz
/// window), and the smaller exponent of a pair is within ~30 of the larger
/// (the pending quotient `bl(q) <= 29` bounds the ratio), so `e_X >= w - 107`:
/// the `exp_range` miss kind (an exponent outside the window) is empty on the
/// support. The terminal values `e_A = 0` / `e_B = 1` need `base = 0`, i.e.
/// `w_a <= 127` (the thin schedule: from row 280; the terminal-aware rows
/// start at 340 - asserted by the driver).
pub(crate) fn exp_base(w: usize) -> usize {
    w.saturating_sub(EXP_SPAN - 1)
}

/// `e - base` mod 2^EXP_BITS (the register value of the true exponent `e`).
pub(crate) fn rebase(e: usize, base: usize) -> usize {
    (e as i64 - base as i64).rem_euclid(EXP_SPAN as i64) as usize
}
/// The aligned scans' window width (design 2.4).
pub(crate) const WINDOW: usize = 32;
/// Packed peak the substeps budget their scratch against: 850 with the 7-bit
/// rebased exponents and `TRAILMIX_Q_CAP=22`, 847 at `TRAILMIX_Q_CAP=19` (design section 5's 866 was the
/// 9-bit, natural-q-envelope layout).
pub(crate) const DEFAULT_QCAP: usize = 838;
/// D0's OR-capture window (design 3.1: the KG ladder over `R1[0..28)`).
pub(crate) const TERM_WINDOW: usize = 28;
/// The widest q register the 5-bit shift word supports on the support
/// (`s2 + carry <= 31`, D8 / D12 reach): `w_q <= 31`.
pub(crate) const MAX_Q_WIDTH: usize = 31;

/// The per-step envelope (module doc).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StepWidths {
    pub step: usize,
    /// `max(env bl A, env bl B)`: the value ring `[0, w_a)`.
    pub w_a: usize,
    /// env bl B alone (M1's ring top is `min(257, w_b + 32)`).
    pub w_b: usize,
    /// `max(env bl ca, env bl cb)` (the ca column already holds `ca_post`):
    /// the coefficient ring `[256 - w_c, 257)`.
    pub w_c: usize,
    /// q's register width: retained `TRAILMIX_Q_CAP`, or the natural envelope
    /// (`packed_q_width`; the driver sizes q from the same function).
    pub w_q: usize,
    /// Schedule low bounds (`thin_lo`): `e_X >= lo_X + 1` on the support.
    pub lo_a: usize,
    pub lo_b: usize,
    pub lo_ca: usize,
    pub lo_cb: usize,
    /// Rotation layers for the division shift `s` and the multiply shift `s2`.
    pub rb_div: usize,
    pub rb_mul: usize,
    /// The raw shift bounds they came from.
    pub s_div_bound: usize,
    pub s2_bound: usize,
}

/// `rb(b)` of `shrunken_pz_pass_step`: bit-length of the bound, 1 for 0.
pub(crate) fn rot_layers(bound: usize) -> usize {
    if bound == 0 { 1 } else { usize::BITS as usize - bound.leading_zeros() as usize }
}

impl StepWidths {
    /// The envelope of prefix row `step` from the active schedule
    /// (`reg_widths` / `shift_bounds`; the thin schedule when
    /// `TRAILMIX_THIN_SCHEDULE=1`, the static tables otherwise), every `lo`
    /// from `thin_lo` (module doc).
    pub(crate) fn from_schedule(step: usize) -> Self {
        let (wa, wb, wca, wcb, _) = reg_widths(step);
        // the q register width: the envelope clamped to TRAILMIX_Q_CAP (the
        // q-clamp lever; `p0_shape::natural_q_width` sizes the register from
        // the same function, and the support model applies the same cap)
        let wq = packed_q_width(step);
        let lo = |w: usize| thin_lo(w.min(u16::MAX as usize) as u16);
        let (sdb, s2b) = shift_bounds(step);
        // Any terminal-aware row may finish with ca = p. Keep its entire
        // coefficient field available, while preserving the original lower
        // bounds (raising an upper bound does not prove a larger lower bound).
        let margin = std::env::var("MIDQ_PACKED_RANGE_MARGIN").ok()
            .map(|s| s.parse::<usize>().expect("nonnegative packed range margin")).unwrap_or(16);
        assert!(margin <= 16, "packed range margin exceeds the 7-bit alignment window");
        // Widen both sides of the value envelope and the coefficient ceiling.
        // Preserve coefficient lower bounds: raising them with the ceiling
        // would exclude faster inputs again.
        let wc = if step >= super::p0_shape::terminal_from() { 256 }
                 else { (wca.max(wcb) + margin).min(256) };
        // Eight upper guard bits remain a uniform widening over the original
        // envelope; coefficients and lower value bounds keep the full margin.
        let value_guard = margin.min(8);
        // Widen every coefficient lower boundary, including M5/M10 and roles.
        let coef_lower_guard = margin.min(4);
        Self::new(step, (wa.max(wb) + value_guard).min(257), (wb + value_guard).min(256), wc, wq, lo(wa).saturating_sub(margin),
                  lo(wb).saturating_sub(margin), lo(wca).saturating_sub(coef_lower_guard),
                  lo(wcb).saturating_sub(coef_lower_guard), sdb, s2b)
    }

    /// Explicit envelope (selftests, synthetic configurations). Widths are
    /// clamped to the rings: `w_a <= 257`, `w_b <= 256`, `w_c <= 256`; each
    /// `lo` to its width.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        step: usize,
        w_a: usize,
        w_b: usize,
        w_c: usize,
        w_q: usize,
        lo_a: usize,
        lo_b: usize,
        lo_ca: usize,
        lo_cb: usize,
        s_div_bound: usize,
        s2_bound: usize,
    ) -> Self {
        let w_a = w_a.clamp(1, RING);
        let w_b = w_b.clamp(1, RING - 1);
        let w_c = w_c.clamp(1, RING - 1);
        StepWidths {
            step,
            w_a,
            w_b,
            w_c,
            w_q,
            lo_a: lo_a.min(w_a - 1),
            lo_b: lo_b.min(w_b - 1),
            lo_ca: lo_ca.min(w_c - 1),
            lo_cb: lo_cb.min(w_c - 1),
            rb_div: rot_layers(s_div_bound),
            rb_mul: rot_layers(s2_bound),
            s_div_bound,
            s2_bound,
        }
    }

    /// The build-time invariants of a packed step (module doc, "q envelope"):
    /// `w_q <= 31`, `w_a - lo_b <= 127` (D11's 7-bit rotation amount) and the
    /// M1 ring inside the 257 wires. Panics with the numbers.
    pub(crate) fn assert_packed_step(&self) {
        assert!(
            self.w_q <= MAX_Q_WIDTH,
            "packed step {}: q envelope {} exceeds {MAX_Q_WIDTH} (s2 + carry must fit the 5-bit shift word)",
            self.step,
            self.w_q
        );
        // The offset is W_A-e_B, not the ring length (which also includes
        // the 32-bit scan window). A longer ring needs no extra address bit.
        assert!(self.w_a - self.lo_b <= 127, "packed step {}: D11 offset W_A-lo_B={} exceeds 127", self.step, self.w_a - self.lo_b);
    }

    /// Rotation layers for M11's amount `D = s2 + carry <= s2_bound + 1`.
    pub(crate) fn rb_mul_plus_carry(&self) -> usize {
        rot_layers(self.s2_bound + 1)
    }

    /// The value pair's exponent base ([`exp_base`] of the value ring top):
    /// `e_A`, `e_B` hold `e - base_v` mod 2^7 during this row.
    pub(crate) fn base_v(&self) -> usize {
        exp_base(self.w_a)
    }

    /// The coefficient pair's exponent base ([`exp_base`] of the coefficient
    /// ring top): `e_ca`, `e_cb` hold `e - base_c` mod 2^7 during this row.
    pub(crate) fn base_c(&self) -> usize {
        exp_base(self.w_c)
    }

    /// Register value of a value exponent `e` in this row's frame.
    pub(crate) fn reb_v(&self, e: usize) -> usize {
        rebase(e, self.base_v())
    }

    /// Register value of a coefficient exponent `e` in this row's frame.
    pub(crate) fn reb_c(&self, e: usize) -> usize {
        rebase(e, self.base_c())
    }

    /// Is the true value exponent `e` representable in this row's frame?
    pub(crate) fn v_in_range(&self, e: usize) -> bool {
        e >= self.base_v() && e < self.base_v() + EXP_SPAN
    }

    /// Is the true coefficient exponent `e` representable in this row's frame?
    pub(crate) fn c_in_range(&self, e: usize) -> bool {
        e >= self.base_c() && e < self.base_c() + EXP_SPAN
    }

    /// The late rows (`lo_b <= 32`, i.e. `w_b <= 110`, rows >= ~310 of the
    /// thin schedule): every window that depended on `lo_b` is widened to the
    /// ring bottom, so the step has NO `lo_b` dependence there - the D4/D9
    /// capture window starts at 1, the D7 zone at wire 1, M1's ring at wire 0,
    /// the role clear's cascade at cell 0 (module doc). Fast-converging inputs
    /// (B narrower than the envelope by more than the clz window, the
    /// terminal / draining rows with B = 1 before `lo_b` reaches 0) are then
    /// on the support instead of `lo_B` / `lo_v` / zone misses; the price is
    /// ~+190 T per row over rows 310-371 (~14k T per traversal, 0.2%).
    pub(crate) fn lo_b_free(&self) -> bool {
        self.lo_b <= WINDOW
    }

    /// Role lower boundary from the uniformly widened coefficient envelope.
    pub(crate) fn role_compute_lo_c(&self) -> usize {
        self.lo_ca.max(self.lo_cb).min(RING - 2)
    }

    /// The role clear's cascade bottom `lo_v` (design 3.3): `max(lo_a, lo_b)`
    /// on the mid rows, 0 on the late rows and on the terminal-aware rows
    /// (draining / frozen rows have `e_A = 0`, `e_B = 1`, so `m' = 1` there).
    pub(crate) fn role_clear_lo_v(&self, terminal_row: bool) -> usize {
        if terminal_row || self.lo_b_free() { 0 } else { self.lo_a.max(self.lo_b).min(RING - 2) }
    }

    // ------------------------------------------------------------ division

    /// D4/D9 cascade bottom (module doc): `max(0, lo_b - 32)`.
    pub(crate) fn div_cascade_lo(&self) -> usize {
        self.lo_b.saturating_sub(WINDOW).min(self.w_a - 1)
    }

    /// D4/D9 capture window (module doc): addresses `e_B` in `[lo, w_a]` with
    /// `lo = lo_b + 1` while `lo_b > 32`, else `cascade_lo + 1 = 1`;
    /// `k = e_B - cascade_lo` cascade cells. The address register is the
    /// rebased `e_B` (`base = base_v`; `capture_compare` clips the window to
    /// the representable addresses).
    pub(crate) fn div_capture_window(&self) -> CaptureWindow {
        let lo_c = self.div_cascade_lo();
        let lo = if self.lo_b > WINDOW { self.lo_b + 1 } else { lo_c + 1 };
        CaptureWindow { lo: lo.min(self.w_a), hi: self.w_a, field: FieldEnd::AddrMinus(lo_c), base: self.base_v() }
    }

    /// Start of D7's masked zone `[start, w_a)` (module doc):
    /// `min(257 - w_c, lo_b + 1)` on the mid rows, 1 on the late rows
    /// ([`Self::lo_b_free`]: every `E >= 1` then visits its toggle leaf), or
    /// `w_a` (empty) when no ca bit can lie in the window.
    /// Never below `base_v`: a field end below the rebase window is
    /// unrepresentable (`exp_range`), so the cells `[.., base_v)` are inside
    /// the field on every representable row and stay plain.
    pub(crate) fn div_zone_start(&self) -> usize {
        let coef_from = RING - self.w_c;
        let start = if coef_from >= self.w_a {
            self.w_a
        } else if self.lo_b_free() {
            1.min(self.w_a)
        } else {
            coef_from.min(self.lo_b + 1).min(self.w_a)
        };
        start.max(self.base_v()).min(self.w_a)
    }

    /// The D7 support predicate of a row with field end `e = e_B + off`: the
    /// toggle leaf lies in the zone, or the zone is empty (no ca bit can lie in
    /// the window, every plain cell above the field sees a gap zero).
    pub(crate) fn div_zone_admits(&self, e: usize) -> bool {
        let z = self.div_zone_start();
        z >= self.w_a || e >= z
    }

    /// D11's ring bottom `L = max(0, lo_b - 32)` (`aligned_scan::top_geometry`).
    pub(crate) fn div_ring_bottom(&self) -> usize {
        super::aligned_scan::top_geometry(self.w_a, self.lo_b).0
    }

    /// D0 window width `n0 = min(28, w_a)`.
    pub(crate) fn div_term_window(&self) -> usize {
        TERM_WINDOW.min(self.w_a)
    }

    /// D11 window width `n_w` (`aligned_scan::top_geometry`).
    pub(crate) fn div_scan_window(&self) -> usize {
        super::aligned_scan::top_geometry(self.w_a, self.lo_b).2
    }

    // ------------------------------------------------------------ multiply

    /// The coefficient ring `[256 - w_c, 257)` as a wire range.
    pub(crate) fn coef_ring(&self) -> std::ops::Range<usize> {
        (RING - 1 - self.w_c)..RING
    }

    /// M5's window is the coefficient ring in bit order (cell `j` = wire
    /// `256 - j`), `w_c + 1` cells.
    pub(crate) fn mul_window_cells(&self) -> usize {
        self.w_c + 1
    }

    /// M5's zone edge (module doc): the zone `[start, w_c + 1)` must hold every
    /// cell whose R1 wire can carry an A bit (`j >= 257 - w_a`) AND its plain
    /// cells `[0, start)` must lie inside cb's field on every support row
    /// (`start <= e_cb`, guaranteed by `e_cb >= lo_cb + 1`). So
    /// `start = min(257 - w_a, lo_cb + 1)`, clamped to the window.
    /// Never below `base_c` (an `e_cb` below the rebase window is
    /// unrepresentable: the cells below `base_c` are inside cb's field on
    /// every representable row and stay plain).
    pub(crate) fn mul_zone_start(&self) -> usize {
        (RING - self.w_a).min(self.lo_cb + 1).max(self.base_c()).min(self.mul_window_cells())
    }

    /// M1's `lo_b`: the schedule's bound, clamped so the 32-window stays below
    /// wire 257 (`aligned_scan_bottom` requires `lo_b + 32 <= 257`; at steps
    /// 0-2 the static `B_LO` is 226-227). Clamping only widens the ring: the
    /// primitive's precondition is `lo_b <= e_B`, and B's low bits wrapping
    /// into the window is the case the `nz` gate handles (refuter 2).
    pub(crate) fn m1_lo_b(&self) -> usize {
        // Every representable e_B is >= base_v >= W_B-127. Keeping this
        // lower edge on wider synthetic schedules bounds the 7-bit offset;
        // terminal-capable (base_v=0) rows still use the unrestricted edge 0.
        if self.lo_b_free() { self.w_b.saturating_sub(EXP_SPAN - 1) }
        else { self.lo_b.min(RING - WINDOW).min(self.w_b) }
    }

    /// M10's address window bottom: the compare `(ca_new >> D) < cb` is
    /// anchored at `e_cb`; the smaller of the two coefficient bounds (both
    /// `<= e_cb - 1`).
    pub(crate) fn m10_lo_c(&self) -> usize {
        self.lo_ca.min(self.lo_cb)
    }

    /// M10's cascade bottom (module doc): 32 cells below [`Self::m10_lo_c`],
    /// so the carry-row tie residue is `<= 2^-33`.
    pub(crate) fn m10_cascade_lo(&self) -> usize {
        self.m10_lo_c().saturating_sub(WINDOW)
    }

    /// M10's capture window: addresses `e_cb` in `[m10_lo_c + 1, w_c]`,
    /// `k = e_cb - cascade_lo` cells.
    pub(crate) fn m10_capture_window(&self) -> CaptureWindow {
        CaptureWindow { lo: self.m10_lo_c() + 1, hi: self.w_c, field: FieldEnd::AddrMinus(self.m10_cascade_lo()), base: self.base_c() }
    }

    /// One line per step for `MIDQ_PACKED_DUMP_SCHED=1` (the support model's
    /// mirror of the built geometry).
    pub(crate) fn dump_line(&self) -> String {
        let win = self.div_capture_window();
        format!(
            "MIDQ_PACKED_SCHED step={} w_a={} w_b={} w_c={} w_q={} lo_a={} lo_b={} lo_ca={} lo_cb={} rb_div={} rb_mul={} s_div_bound={} s2_bound={} base_v={} base_c={} | D4/D9 cascade_lo={} addr=[{},{}] D7 zone_start={} D11 ring=[{},{}) n_w={} D0 n0={} | M1 lo_b={} M5 zone_start={} M10 lo_c={} cascade_lo={}",
            self.step, self.w_a, self.w_b, self.w_c, self.w_q, self.lo_a, self.lo_b, self.lo_ca, self.lo_cb, self.rb_div, self.rb_mul,
            self.s_div_bound, self.s2_bound, self.base_v(), self.base_c(), self.div_cascade_lo(), win.lo, win.hi, self.div_zone_start(), self.div_ring_bottom(), self.w_a,
            self.div_scan_window(), self.div_term_window(), self.m1_lo_b(), self.mul_zone_start(), self.m10_lo_c(), self.m10_cascade_lo()
        )
    }
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(default)
}

/// Scratch wires a substep may allocate right now without exceeding the packed
/// peak: `MIDQ_PACKED_QCAP` (default [`DEFAULT_QCAP`]) minus the live count;
/// `MIDQ_PACKED_CTZ_ROOM=<n>` overrides the result (measurement / selftests).
pub(crate) fn scratch_room(c: &mut Circuit) -> usize {
    if let Some(room) = std::env::var("MIDQ_PACKED_CTZ_ROOM").ok().and_then(|s| s.parse::<usize>().ok()) {
        return room;
    }
    c.flush_pending_frees();
    env_usize("MIDQ_PACKED_QCAP", DEFAULT_QCAP).saturating_sub(c.b.active_qubits as usize)
}
