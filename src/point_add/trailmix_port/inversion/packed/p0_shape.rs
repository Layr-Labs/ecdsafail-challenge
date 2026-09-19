//! P0 shape build (tools/spike/packed_design.md section 10, "P0" row).
//!
//! The prefix registers are the packed shape - `R1 = [A | gap | cb]`,
//! `R2 = [B | gap | ca]` on two fixed 257-wire rings, four persisted 9-bit
//! exponents, q at its per-step natural envelope width (no
//! `TRAILMIX_Q_TARGET` budget) - with NO-OP substeps: each division/multiply
//! item allocates exactly the scratch the design says the real primitive
//! will (section 5: engine 8, f/t/carry 3, KG 3 + pos 6, t7 7, nz 1, bc.c 1,
//! term 1) and frees it again. Everything around the substeps is real:
//! role/swap (257 + 18 cswaps), the terminal counter from
//! `MIDQ_PREFIX_TERMINAL_FROM` (default [`DEFAULT_TERMINAL_FROM`] = 340) with the popcount cache erased
//! there, the S_0 entry (one ungated 256-wide `bit_length_lean` for e_B), the
//! cut-530 teardown / re-creation, and the coefficients-first unpack/repack
//! at the ping-pong handoff (cut 384 / 480) with the tail unchanged.
//!
//! Correctness is NOT a goal of this branch: only the allocation timeline is.
//! The per-step assertion of section 5 (no scan moment above the adder
//! moment) is measured from `c.b.active_qubits` at each moment and reported
//! as `MIDQ_P0_MOMENTS` / `MIDQ_P0_STEP` lines on stderr.
//!
//! Enabled by `MIDQ_PACKED_PREFIX=1` (the branch default).
//!
//! P4 (`driver.rs`): the substep stubs are replaced by the real driver
//! (`driver::pass_step`: exact role pair, `multiply_forward`/`_backward`,
//! `division_forward`/`_backward`, the `term` wire, the same swap / done
//! counter); `MIDQ_PACKED_STUBS=1` restores the stub timeline. The moment
//! census of the real build comes from `TRACE_PHASE_ACTIVE=1`
//! (`driver::census`); `MIDQ_TRACE_PZ_STEPS=1` prints the per-step Toffoli
//! (CCX + CCZ) of each direction (`MIDQ_PZ_STEP`) and the cumulative sums
//! (`MIDQ_PZ_PREFIX`).

use super::super::*;
use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{
    packed_q_width, SHRUNKEN_PZ_NSTEPS,
};

pub(crate) fn enabled() -> bool {
    std::env::var("MIDQ_PACKED_PREFIX").ok().as_deref() == Some("1")
}

/// First terminal-aware row (`MIDQ_PREFIX_TERMINAL_FROM`, default
/// [`DEFAULT_TERMINAL_FROM`]).
pub(crate) fn terminal_from() -> usize {
    env_usize("MIDQ_PREFIX_TERMINAL_FROM", DEFAULT_TERMINAL_FROM)
}

/// The branch default of `MIDQ_PREFIX_TERMINAL_FROM` (review 2026-09-14,
/// finding 4). The design's 365 ("1M model first termination 365") was wrong:
/// the 262k review pool had an input terminating at row 359, and the
/// `tools/spike/term_first.py` (R:/Coding/shor2; the verbatim `pz_prefix` recurrence, 4M
/// inputs, seeds 2026/2027/2028) measured the first terminal division at
/// **352** (1 in 2M; 356, 361, 362, 362, 363, 364 next; 8/4M = 2e-6 per input
/// below 365). A terminal division before FROM is the `term_row` miss (frozen
/// rows would run a multiply with q = 0, D11 without the override).
///
/// What bounds it: the last draining row of every terminating input has
/// `ca = p` (256 bits), and the seed-278 thin schedule's coefficient envelope
/// reaches 256 only at row 371 (`MIDQ_PACKED_DUMP_SCHED=1`), so an input frozen
/// before ~372 is a `width_c` miss whatever FROM is (29 of the 35 early
/// terminators of the 4M draw, `review_cases.rs` round trip (c)); the drain
/// span is `popcount(q_term) + 1 <= w_q + 1 = 24` there, so for any FROM <= 347
/// no `term_row` miss can occur on an otherwise on-support input. 340 keeps 7
/// rows of margin (a regenerated schedule moves the 256 row by a few rows);
/// each terminal-aware row costs ~+500 T per direction (D0 x 2, the widened
/// role clear, the done counter: 25 rows below 365 = ~50k T per point add,
/// 0.2%); every row >= 314 keeps the 866 peak (rows 314-364 have q <= 23 in
/// the thin profile, so the `term` wire stays under the q = 29 adder moment of
/// rows 284-313); the 8-bit counter covers `530 - 340 = 190 < 256` frozen rows.
pub(super) const DEFAULT_TERMINAL_FROM: usize = 340;

/// `MIDQ_PACKED_DUMP_SCHED=1`: one `MIDQ_PACKED_SCHED` line per row with the
/// built geometry (the support model's mirror), printed before the first row.
fn dump_sched() -> bool {
    std::env::var_os("MIDQ_PACKED_DUMP_SCHED").is_some()
}

fn trace_steps() -> bool {
    std::env::var_os("MIDQ_P0_TRACE").is_some()
}

use super::sched::{rebase, EXP_BITS};
const RING: usize = 257;

/// Number of prefix rows for the configured route.
fn prefix_steps() -> usize {
    if midq_tail_enabled() { MIDQ_PZ_CUT } else { SHRUNKEN_PZ_NSTEPS }
}

/// The q register width of row `i`: the configured capacity is retained
/// across all rows so late pending quotient bits are not discarded.
pub(super) fn natural_q_width(i: usize) -> usize {
    packed_q_width(i).max(1)
}

/// The exponent bases of row `i` (`sched.rs`): `(base_v, base_c)`.
fn exp_bases(i: usize) -> (usize, usize) {
    let sched = super::sched::StepWidths::from_schedule(i);
    (sched.base_v(), sched.base_c())
}

/// Move the four exponent registers from the frame of row `from` to the frame
/// of row `to` (`e_reg += base(from) - base(to)`, unconditional, mod 2^7, one
/// `add_const` per register - the per-step rebase of the 7-bit exponent lever).
/// Frozen rows are rebased too (their `e_A = 0` stays `0 - base_v`, which is
/// 0 on every terminal-aware row); the operation is its own mirror with the
/// rows swapped.
fn rebase_exponents(c: &mut Circuit, p: &Packed, from: usize, to: usize) {
    let (fv, fc) = exp_bases(from);
    let (tv, tc) = exp_bases(to);
    let dv = fv as i64 - tv as i64;
    let dc = fc as i64 - tc as i64;
    if dv == 0 && dc == 0 {
        return;
    }
    let sec = c.push_section("pk.rebase");
    if dv != 0 {
        super::exponent_arith::add_const(c, p.e_a(), dv);
        super::exponent_arith::add_const(c, p.e_b(), dv);
    }
    if dc != 0 {
        super::exponent_arith::add_const(c, p.e_ca(), dc);
        super::exponent_arith::add_const(c, p.e_cb(), dc);
    }
    c.pop_section(&sec);
}

/// Popcount cache in the idle counter on the no-terminal rows (rows < FROM).
pub(crate) fn popcount_on(counter: &[QReg]) -> bool {
    std::env::var("MIDQ_PREFIX_POPCOUNT").ok().as_deref() == Some("1")
        && counter.len() == counter_tape::BITS
        && counter.len() >= prefix_popcount::BITS
        && (0..prefix_steps()).all(|i| natural_q_width(i) < (1 << prefix_popcount::BITS))
}

/// The packed PZ state. `ex1 = [e_A | e_cb]` pairs with R1, `ex2 = [e_B | e_ca]`
/// with R2, so a role swap is `cswap` over (R1, R2) and (ex1, ex2).
pub(crate) struct Packed {
    pub(super) r1: Vec<QReg>,
    pub(super) r2: Vec<QReg>,
    pub(super) ex1: Vec<QReg>,
    pub(super) ex2: Vec<QReg>,
    pub(super) q: Vec<QReg>,
    pub(super) counter: Vec<QReg>,
    pub(super) s_rot: Vec<QReg>,
    pub(super) off: Option<QReg>,
    pub(super) parity: Option<BorrowedQReg<'static>>,
}

impl Packed {
    pub(super) fn e_a(&self) -> &[QReg] { &self.ex1[..EXP_BITS] }
    pub(super) fn e_cb(&self) -> &[QReg] { &self.ex1[EXP_BITS..] }
    pub(super) fn e_b(&self) -> &[QReg] { &self.ex2[..EXP_BITS] }
    pub(super) fn e_ca(&self) -> &[QReg] { &self.ex2[EXP_BITS..] }
}

/// Per-build moment maxima (design section 5 acceptance).
#[derive(Default)]
struct Moments {
    adder: u32,
    adder_step: usize,
    scan: u32,
    scan_step: usize,
    scan_kind: &'static str,
    role: u32,
    swap: u32,
    other: u32,
    other_kind: &'static str,
    planner: u32,
    planner_kind: &'static str,
    violations: usize,
    steps: usize,
    /// Real substeps (`driver.rs`) rather than the P0 stubs.
    real: bool,
    /// `TRACE_PHASE_ACTIVE` was set (the real census needs it).
    traced: bool,
}

thread_local! {
    static MOMENTS: std::cell::RefCell<Moments> = std::cell::RefCell::new(Moments::default());
}

fn active(c: &Circuit) -> u32 { c.b.active_qubits }

fn load_p(c: &mut Circuit, reg: &[QReg]) {
    let p_bytes = crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;
    for (j, q) in reg.iter().enumerate() {
        if j < 256 && (p_bytes[j / 8] >> (j % 8)) & 1 == 1 {
            c.x(q);
        }
    }
}

/// `s += bl(src) - base` (dec: `s -= bl(src) - base`), mod 2^|s|, by the plain
/// KG ladder of `bit_length_lean_middle` with the `+1` folded into X-brackets
/// (`s -= pos + 1` is `s += ~pos`; `s += pos + 1` is `~s += ~pos`), so the
/// scratch is the 9-bit `pos` (`|n> = 256` must fit it) + KG ancillae only
/// (no `inc_khattar_gidney` ancillae); the low `|s|` bits of `pos` are added
/// (the 7-bit rebased registers: `bl mod 128`), then the base is folded in by
/// one unconditional `add_const` (before the ladder when clearing). Every
/// packed-prefix exponent scan (S_0, teardown, unpack/repack) uses it.
fn exp_scan(c: &mut Circuit, src: &[&QReg], s: &[QReg], base: usize, dec: bool, carry: Option<&QReg>) {
    let n = src.len();
    if n == 0 { return; }
    let sec = c.push_section("p.bitlen");
    if dec && base != 0 {
        super::exponent_arith::add_const(c, s, base as i64);
    }
    let pos_bits = s.len().max((usize::BITS - n.leading_zeros()) as usize);
    let pos = c.alloc_qreg_bits("bll.pos", pos_bits);
    xor_const(c, &pos, n);
    with_plain_ladder(c, |c| {
        bit_length_lean_middle(c, src, &pos, |c| {
            if !dec { for q in s { c.x(q); } }
            for q in &pos { c.x(q); }
            let sref: Vec<&QReg> = s.iter().collect();
            let pref: Vec<&QReg> = pos[..s.len()].iter().collect();
            add_refs(c, &sref, &pref, carry);
            for q in &pos { c.x(q); }
            if !dec { for q in s { c.x(q); } }
            true
        });
    });
    xor_const(c, &pos, n);
    for q in pos { c.zero_and_free(q); }
    if !dec && base != 0 {
        super::exponent_arith::add_const(c, s, -(base as i64));
    }
    c.pop_section(&sec);
}

/// Force the plain KG ladder for the packed exponent scans so the moment
/// reported is the design's (KG ancillae + pos 9), not a cap-filler.
fn with_plain_ladder(c: &mut Circuit, body: impl FnOnce(&mut Circuit)) {
    let saved = std::env::var("MIDQ_CHUNKED_PREFIX").ok();
    std::env::set_var("MIDQ_CHUNKED_PREFIX", "0");
    body(c);
    match saved {
        Some(v) => std::env::set_var("MIDQ_CHUNKED_PREFIX", v),
        None => std::env::remove_var("MIDQ_CHUNKED_PREFIX"),
    }
}

// ---------------------------------------------------------------------------
// S_0 entry / exit (both cuts) and the cut-530 teardown
// ---------------------------------------------------------------------------

/// PRE: `dx` = |x| on 257 wires (wire 256 clean). POST: `Packed` in S_0:
/// R1 = [p | cb = 1 at wire 256], R2 = dx (= [B | ca = 0]), e_A = 256,
/// e_B = bl(B), e_ca = 0, e_cb = 1 (all four in the frame of row 0:
/// `e - base(0)` mod 2^7), q = 0, counter = 0, parity = 1.
fn enter_s0(c: &mut Circuit, dx: Vec<QReg>, passenger_carry: Option<&QReg>, tag: &str) -> Packed {
    assert_eq!(dx.len(), RING);
    let sec = c.push_section("pk.s0");
    let r2 = dx;
    let r1 = c.alloc_qreg_bits(&format!("{tag}.R1"), RING);
    load_p(c, &r1[..256]); // A = p
    c.x(&r1[256]); // cb = 1 (LSB anchored at wire 256)
    let mut ex1 = c.alloc_qreg_bits(&format!("{tag}.eA"), EXP_BITS);
    ex1.extend(c.alloc_qreg_bits(&format!("{tag}.ecb"), EXP_BITS));
    let mut ex2 = c.alloc_qreg_bits(&format!("{tag}.eB"), EXP_BITS);
    ex2.extend(c.alloc_qreg_bits(&format!("{tag}.eca"), EXP_BITS));
    let (bv0, bc0) = exp_bases(0);
    xor_const(c, &ex1[..EXP_BITS], rebase(256, bv0)); // e_A = 256
    xor_const(c, &ex1[EXP_BITS..], rebase(1, bc0)); // e_cb = 1
    xor_const(c, &ex2[EXP_BITS..], rebase(0, bc0)); // e_ca = 0 (base_c(0) = 0 on the thin schedule)
    // e_B = bl(B): one ungated 256-wide scan (B < p < 2^256, wire 256 is 0).
    {
        let src: Vec<&QReg> = r2[..256].iter().collect();
        exp_scan(c, &src, &ex2[..EXP_BITS], bv0, false, passenger_carry);
    }
    let q = c.alloc_qreg_bits(&format!("{tag}.q"), natural_q_width(0));
    let s_rot = c.alloc_qreg_bits(&format!("{tag}.srot"), trailmix_srot_width());
    let off = Some(c.alloc_qreg(&format!("{tag}.off")));
    let parity_q = c.alloc_qreg(&format!("{tag}.par"));
    c.x(&parity_q);
    let counter = c.alloc_qreg_bits(&format!("{tag}.ctr"), trailmix_counter_width());
    c.pop_section(&sec);
    Packed {
        r1,
        r2,
        ex1,
        ex2,
        q,
        counter,
        s_rot,
        off,
        parity: Some(BorrowedQReg::Owned(parity_q)),
    }
}

/// Mirror of `enter_s0`: PRE the S_0 state; frees everything but R2 (= dx).
fn exit_s0(c: &mut Circuit, mut p: Packed, passenger_carry: Option<&QReg>) -> Vec<QReg> {
    let sec = c.push_section("pk.s0.exit");
    let (bv0, bc0) = exp_bases(0);
    for q in p.q.drain(..).chain(p.s_rot.drain(..)).chain(p.counter.drain(..)) {
        c.zero_and_free(q);
    }
    c.zero_and_free(p.off.take().expect("packed offset scratch"));
    let par = sign_storage::owned(&mut p.parity);
    c.x(&par);
    c.zero_and_free(par);
    {
        let src: Vec<&QReg> = p.r2[..256].iter().collect();
        exp_scan(c, &src, &p.ex2[..EXP_BITS], bv0, true, passenger_carry);
    }
    xor_const(c, &p.ex1[..EXP_BITS], rebase(256, bv0));
    xor_const(c, &p.ex1[EXP_BITS..], rebase(1, bc0));
    xor_const(c, &p.ex2[EXP_BITS..], rebase(0, bc0));
    c.x(&p.r1[256]);
    load_p(c, &p.r1[..256]);
    for q in p.r1.into_iter().chain(p.ex1).chain(p.ex2).chain(p.q) {
        c.zero_and_free(q);
    }
    for q in p.s_rot.into_iter().chain(p.counter) {
        c.zero_and_free(q);
    }
    c.pop_section(&sec);
    p.r2
}

/// Cut-530 teardown (design section 6): at the terminal R1 = [0 | x^-1
/// downward], R2 = [1 at wire 0 | p downward], e_A = 0, e_B = 1, e_ca = 256,
/// e_cb = bl(x^-1). Frees R2, the exponents and q; returns `cb` = the reversed
/// R1 (257 LSB-first wires, 0 T) for `mod_mul_rfold_mbu`. The counter, s_rot,
/// off and parity stay live.
fn teardown_530(c: &mut Circuit, p: &mut Packed, passenger_carry: Option<&QReg>) -> Vec<QReg> {
    let sec = c.push_section("pk.teardown");
    for q in std::mem::take(&mut p.q) { c.zero_and_free(q); }
    let (bv, bc) = exp_bases(prefix_steps() - 1); // the frame of the last row
    // e_cb := 0 by one ungated 256-wide scan of the reversed R1 (cb < 2^256).
    {
        let src: Vec<&QReg> = p.r1[1..].iter().rev().collect();
        exp_scan(c, &src, &p.ex1[EXP_BITS..], bc, true, passenger_carry);
    }
    xor_const(c, &p.ex2[..EXP_BITS], rebase(1, bv)); // e_B: 1 -> 0
    xor_const(c, &p.ex2[EXP_BITS..], rebase(256, bc)); // e_ca: 256 -> 0
    xor_const(c, &p.ex1[..EXP_BITS], rebase(0, bv)); // e_A: 0 -> 0 (base_v = 0 at the terminal rows)
    for q in std::mem::take(&mut p.ex1).into_iter().chain(std::mem::take(&mut p.ex2)) {
        c.zero_and_free(q);
    }
    c.x(&p.r2[0]); // B: 1 -> 0
    {
        let rev: Vec<QReg> = std::mem::take(&mut p.r2).into_iter().rev().collect();
        load_p(c, &rev); // ca: p -> 0
        for q in rev { c.zero_and_free(q); }
    }
    let cb: Vec<QReg> = std::mem::take(&mut p.r1).into_iter().rev().collect();
    c.pop_section(&sec);
    cb
}

/// Mirror of `teardown_530` before the backward pass.
fn recreate_530(c: &mut Circuit, p: &mut Packed, cb: Vec<QReg>, passenger_carry: Option<&QReg>, tag: &str) {
    let sec = c.push_section("pk.recreate");
    assert_eq!(cb.len(), RING);
    p.r1 = cb.into_iter().rev().collect();
    {
        let mut rev = c.alloc_qreg_bits(&format!("{tag}.R2"), RING);
        load_p(c, &rev); // ca = p (downward from wire 256)
        rev.reverse();
        p.r2 = rev;
        c.x(&p.r2[0]); // B = 1
    }
    p.ex1 = c.alloc_qreg_bits(&format!("{tag}.eA"), EXP_BITS);
    p.ex1.extend(c.alloc_qreg_bits(&format!("{tag}.ecb"), EXP_BITS));
    p.ex2 = c.alloc_qreg_bits(&format!("{tag}.eB"), EXP_BITS);
    p.ex2.extend(c.alloc_qreg_bits(&format!("{tag}.eca"), EXP_BITS));
    let (bv, bc) = exp_bases(prefix_steps() - 1);
    xor_const(c, &p.ex1[..EXP_BITS], rebase(0, bv));
    xor_const(c, &p.ex2[..EXP_BITS], rebase(1, bv));
    xor_const(c, &p.ex2[EXP_BITS..], rebase(256, bc));
    {
        let src: Vec<&QReg> = p.r1[1..].iter().rev().collect();
        exp_scan(c, &src, &p.ex1[EXP_BITS..], bc, false, passenger_carry);
    }
    p.q = c.alloc_qreg_bits(&format!("{tag}.q"), natural_q_width(prefix_steps() - 1));
    c.pop_section(&sec);
}

// ---------------------------------------------------------------------------
// Substep stubs (allocation timeline only)
// ---------------------------------------------------------------------------

struct Scratch(Vec<QReg>);

fn take(c: &mut Circuit, name: &str, n: usize) -> Scratch {
    Scratch(c.alloc_qreg_bits(name, n))
}

fn give(c: &mut Circuit, s: Scratch) {
    for q in s.0 { c.zero_and_free(q); }
}

fn note_scan(c: &Circuit, kind: &'static str, step: usize) {
    let a = active(c);
    MOMENTS.with(|m| {
        let mut m = m.borrow_mut();
        if a > m.scan { m.scan = a; m.scan_step = step; m.scan_kind = kind; }
    });
}

fn note_adder(c: &Circuit, step: usize) -> u32 {
    let a = active(c);
    MOMENTS.with(|m| {
        let mut m = m.borrow_mut();
        if a > m.adder { m.adder = a; m.adder_step = step; }
    });
    a
}

/// Aligned-window scan moment (D11 / M1 / handoff scans): the 7-bit rotation
/// amount `t7` is live during the sub-ring rotation only; the ladder holds
/// KG 3 + pos 6 (+ nz 1 + bc.c 1 for M1's two-sided sentinel).
fn scan_stub(c: &mut Circuit, kind: &'static str, step: usize, with_nz: bool) -> u32 {
    let t7 = take(c, "pk.t7", 7);
    give(c, t7); // rotate, uncompute t7
    let kg = take(c, "pk.kganc", 3);
    let pos = take(c, "pk.pos", 6);
    let nz = with_nz.then(|| take(c, "pk.nz", 1));
    let bcc = with_nz.then(|| take(c, "bc.c", 1));
    note_scan(c, kind, step);
    let peak = active(c);
    if let Some(b) = bcc { give(c, b); }
    if let Some(n) = nz { give(c, n); }
    give(c, pos);
    give(c, kg);
    let t7 = take(c, "pk.t7", 7);
    give(c, t7); // rotate back
    peak
}

/// Masked-adder moment (D7 / M5): DFS engine 8 + thermometer f, masked t,
/// Cuccaro carry (3).
fn adder_stub(c: &mut Circuit, step: usize) -> u32 {
    let eng = take(c, "pk.eng", 8);
    let ftc = take(c, "pk.ftc", 3);
    let peak = note_adder(c, step);
    give(c, ftc);
    give(c, eng);
    peak
}

/// Capture compare (D4 / D9 / M10): engine 8 + bc.c 1, flag written directly.
fn capture_stub(c: &mut Circuit, kind: &'static str, step: usize) {
    let eng = take(c, "pk.eng", 8);
    let bcc = take(c, "bc.c", 1);
    note_scan(c, kind, step);
    give(c, bcc);
    give(c, eng);
}

/// Multiply M1..M12 (design 3.2) as an allocation timeline.
fn multiply_stub(c: &mut Circuit, step: usize) -> (u32, u32) {
    let sec = c.push_section("pk.mul");
    let s1 = c.push_section("M1.scan");
    let scan = scan_stub(c, "M1", step, true);
    c.pop_section(&s1);
    let s5 = c.push_section("M5.adder");
    let adder = adder_stub(c, step);
    c.pop_section(&s5);
    let s10 = c.push_section("M10.capture");
    capture_stub(c, "M10", step);
    c.pop_section(&s10);
    c.pop_section(&sec);
    (scan, adder)
}

/// Division D0..D12 (design 3.1): `term` (rows >= FROM) is live from its
/// compute after D1 to its clear between D10 and D12, i.e. across D7.
fn division_stub(c: &mut Circuit, step: usize, terminal_row: bool) -> (u32, u32) {
    let sec = c.push_section("pk.div");
    let mut term: Option<Scratch> = None;
    let mut scan_max = 0u32;
    if terminal_row {
        let s0 = c.push_section("D0.term");
        let eq1 = take(c, "pk.eq1", 1);
        let root = take(c, "pk.root", 1);
        let t = take(c, "pk.term", 1);
        let eng = take(c, "pk.eng", 5);
        let kg = take(c, "pk.kganc", 3);
        note_scan(c, "D0", step);
        scan_max = scan_max.max(active(c));
        give(c, kg);
        give(c, eng);
        give(c, root);
        give(c, eq1);
        term = Some(t);
        c.pop_section(&s0);
    }
    let s4 = c.push_section("D4.capture");
    capture_stub(c, "D4", step);
    c.pop_section(&s4);
    let s7 = c.push_section("D7.adder");
    let adder = adder_stub(c, step);
    c.pop_section(&s7);
    let s9 = c.push_section("D9.capture");
    capture_stub(c, "D9", step);
    c.pop_section(&s9);
    let s11 = c.push_section("D11.scan");
    scan_max = scan_max.max(scan_stub(c, "D11", step, false));
    c.pop_section(&s11);
    if let Some(t) = term { give(c, t); }
    c.pop_section(&sec);
    (scan_max, adder)
}

// ---------------------------------------------------------------------------
// Role compare / swap (real cswaps, stubbed compares)
// ---------------------------------------------------------------------------

/// Role compute (design 3.3): `c = [e_ca < e_cb]` (real 9-bit borrow compare),
/// max-by-cswap, the capture compare over R1 vs R2 (stub: engine 8 + bc.c),
/// undo.
fn role_compute_stub(c: &mut Circuit, p: &Packed, role: &QReg, step: usize) -> u32 {
    let sec = c.push_section("pk.role");
    let cflag = c.alloc_qreg("pk.rc.c");
    let ecar: Vec<&QReg> = p.e_ca().iter().collect();
    let ecbr: Vec<&QReg> = p.e_cb().iter().collect();
    borrow_compare_refs(c, &ecar, &ecbr, &cflag);
    c.x(&cflag);
    for (a, b) in p.e_ca().iter().zip(p.e_cb()) { c.cswap(&cflag, a, b); }
    let eng = take(c, "pk.eng", 8);
    let bcc = take(c, "bc.c", 1);
    note_scan(c, "role", step);
    let moment = active(c);
    MOMENTS.with(|m| { let mut m = m.borrow_mut(); m.role = m.role.max(moment); });
    // the capture writes `role` directly; the stub touches it once
    c.cx(&bcc.0[0], role);
    give(c, bcc);
    give(c, eng);
    for (a, b) in p.e_ca().iter().zip(p.e_cb()) { c.cswap(&cflag, a, b); }
    c.x(&cflag);
    borrow_compare_refs(c, &ecar, &ecbr, &cflag);
    c.zero_and_free(cflag);
    c.pop_section(&sec);
    moment
}

/// Role clear (design 3.3): the same construction on the coefficients with
/// `m' = max(e_A, e_B)`.
fn role_clear_stub(c: &mut Circuit, p: &Packed, role: &QReg, step: usize) -> u32 {
    let sec = c.push_section("pk.roleclr");
    let cflag = c.alloc_qreg("pk.rc.c");
    let ear: Vec<&QReg> = p.e_a().iter().collect();
    let ebr: Vec<&QReg> = p.e_b().iter().collect();
    borrow_compare_refs(c, &ear, &ebr, &cflag);
    c.x(&cflag);
    for (a, b) in p.e_a().iter().zip(p.e_b()) { c.cswap(&cflag, a, b); }
    let eng = take(c, "pk.eng", 8);
    let bcc = take(c, "bc.c", 1);
    note_scan(c, "roleclr", step);
    let moment = active(c);
    MOMENTS.with(|m| { let mut m = m.borrow_mut(); m.role = m.role.max(moment); });
    c.cx(&bcc.0[0], role);
    give(c, bcc);
    give(c, eng);
    for (a, b) in p.e_a().iter().zip(p.e_b()) { c.cswap(&cflag, a, b); }
    c.x(&cflag);
    borrow_compare_refs(c, &ear, &ebr, &cflag);
    c.zero_and_free(cflag);
    c.pop_section(&sec);
    moment
}

/// Terminal-aware swap + done counter (rows >= FROM): `a_nonzero = OR(e_A)`
/// (9-bit) replaces `or_nonzero(A)` over the value window.
pub(super) fn swap_and_done_forward(c: &mut Circuit, p: &Packed, active_q: QReg, no_terminal: bool) {
    let sec = c.push_section("pk.swap");
    let parity = p.parity.as_deref().expect("packed parity is live");
    if no_terminal {
        let zero_word: &[QReg] = if popcount_on(&p.counter) {
            &p.counter[..prefix_popcount::BITS]
        } else {
            &p.q
        };
        swap_no_terminal(c, &p.r1, &p.r2, &p.ex1, &p.ex2, zero_word, parity);
        MOMENTS.with(|m| { let mut m = m.borrow_mut(); m.swap = m.swap.max(active(c) + 1); });
        uncompute_active(c, &[], &active_q);
        c.zero_and_free(active_q);
        c.pop_section(&sec);
        return;
    }
    let q_zero = c.alloc_qreg("sw.qz");
    let a_nonzero = c.alloc_qreg("sw.anz");
    or_is_zero(c, &p.q, &q_zero);
    or_nonzero(c, p.e_a(), &a_nonzero);
    swap_with_held_predicates(c, &p.r1, &p.r2, &p.ex1, &p.ex2, parity, &active_q, &q_zero, &a_nonzero);
    MOMENTS.with(|m| { let mut m = m.borrow_mut(); m.swap = m.swap.max(active(c) + 2); });
    uncompute_active(c, &p.counter, &active_q);
    c.zero_and_free(active_q);
    done_counter_from_swap_predicates(c, &q_zero, &a_nonzero, &p.counter, false);
    clear_zero_predicate(c, p.e_a(), &a_nonzero, true);
    clear_zero_predicate(c, &p.q, &q_zero, false);
    c.zero_and_free(a_nonzero);
    c.zero_and_free(q_zero);
    c.pop_section(&sec);
}

pub(super) fn undo_done_and_swap(c: &mut Circuit, p: &Packed, no_terminal: bool) -> QReg {
    let sec = c.push_section("pk.swap");
    let parity = p.parity.as_deref().expect("packed parity is live");
    if no_terminal {
        let zero_word: &[QReg] = if popcount_on(&p.counter) {
            &p.counter[..prefix_popcount::BITS]
        } else {
            &p.q
        };
        swap_no_terminal(c, &p.r1, &p.r2, &p.ex1, &p.ex2, zero_word, parity);
        let a = compute_active(c, &[]);
        c.pop_section(&sec);
        return a;
    }
    let q_zero = c.alloc_qreg("sw.qz");
    let a_nonzero = c.alloc_qreg("sw.anz");
    or_is_zero(c, &p.q, &q_zero);
    or_nonzero(c, p.e_a(), &a_nonzero);
    done_counter_from_swap_predicates(c, &q_zero, &a_nonzero, &p.counter, true);
    let active_q = compute_active(c, &p.counter);
    swap_with_held_predicates(c, &p.r1, &p.r2, &p.ex1, &p.ex2, parity, &active_q, &q_zero, &a_nonzero);
    clear_zero_predicate(c, p.e_a(), &a_nonzero, true);
    clear_zero_predicate(c, &p.q, &q_zero, false);
    c.zero_and_free(a_nonzero);
    c.zero_and_free(q_zero);
    c.pop_section(&sec);
    active_q
}

// ---------------------------------------------------------------------------
// Per-step driver
// ---------------------------------------------------------------------------

/// One prefix row: the real driver (`driver::pass_step`), or the P0 stubs
/// under `MIDQ_PACKED_STUBS=1`.
fn pass_step(c: &mut Circuit, p: &Packed, i: usize, inverse: bool) {
    if super::driver::stubs_enabled() {
        pass_step_stub(c, p, i, inverse);
        return;
    }
    let m = super::driver::pass_step(c, p, i, inverse);
    MOMENTS.with(|mm| {
        let mut mm = mm.borrow_mut();
        mm.steps += 1;
        mm.real = true;
        mm.traced = m.traced;
        if !m.traced { return; }
        if m.adder > mm.adder { mm.adder = m.adder; mm.adder_step = i; }
        if m.scan > mm.scan { mm.scan = m.scan; mm.scan_step = i; mm.scan_kind = m.scan_kind; }
        mm.role = mm.role.max(m.role);
        mm.swap = mm.swap.max(m.swap);
        if m.other > mm.other { mm.other = m.other; mm.other_kind = m.other_kind; }
        if m.planner > mm.planner { mm.planner = m.planner; mm.planner_kind = m.planner_kind; }
        if m.scan.max(m.role) > m.adder { mm.violations += 1; }
    });
    if trace_steps() && m.traced {
        eprintln!(
            "MIDQ_P0_STEP dir={} step={i} q={} adder={} ({}) scan={} ({}) role={} swap={} other={} ({}) planner={} ({}) {}",
            if inverse { "bwd" } else { "fwd" },
            p.q.len(), m.adder, m.adder_kind, m.scan, m.scan_kind, m.role, m.swap, m.other, m.other_kind, m.planner, m.planner_kind,
            if m.scan.max(m.role) > m.adder { "VIOLATION" } else { "ok" }
        );
    }
}

fn pass_step_stub(c: &mut Circuit, p: &Packed, i: usize, inverse: bool) {
    let no_terminal = i < terminal_from();
    let terminal_row = !no_terminal;
    let pop = popcount_on(&p.counter);
    let (scan_m, adder_m, scan_d, adder_d, role_a, role_b);
    if inverse {
        let active_q = undo_done_and_swap(c, p, no_terminal);
        let role = c.alloc_qreg("cross.role");
        role_b = role_clear_stub(c, p, &role, i);
        let div_control = HybridGateControl::new(&active_q, &role);
        div_control.materialize(c);
        (scan_d, adder_d) = division_stub(c, i, terminal_row);
        div_control.release(c);
        c.x(&role);
        let mul_control = HybridGateControl::new(&active_q, &role);
        mul_control.materialize(c);
        (scan_m, adder_m) = multiply_stub(c, i);
        mul_control.release(c);
        if no_terminal && pop {
            prefix_popcount::update(c, &p.counter, &role, &active_q, true);
        }
        role_a = role_compute_stub(c, p, &role, i);
        c.zero_and_free(role);
        let active_counter: &[QReg] = if no_terminal { &[] } else { &p.counter };
        uncompute_active(c, active_counter, &active_q);
        c.zero_and_free(active_q);
    } else {
        let active_counter: &[QReg] = if no_terminal { &[] } else { &p.counter };
        let active_q = compute_active(c, active_counter);
        let role = c.alloc_qreg("cross.role");
        role_a = role_compute_stub(c, p, &role, i);
        if no_terminal && pop {
            prefix_popcount::update(c, &p.counter, &role, &active_q, false);
        }
        let mul_control = HybridGateControl::new(&active_q, &role);
        mul_control.materialize(c);
        (scan_m, adder_m) = multiply_stub(c, i);
        mul_control.release(c);
        c.x(&role);
        let div_control = HybridGateControl::new(&active_q, &role);
        div_control.materialize(c);
        (scan_d, adder_d) = division_stub(c, i, terminal_row);
        div_control.release(c);
        role_b = role_clear_stub(c, p, &role, i);
        c.zero_and_free(role);
        swap_and_done_forward(c, p, active_q, no_terminal);
    }
    let adder = adder_m.max(adder_d);
    let scan = scan_m.max(scan_d).max(role_a).max(role_b);
    MOMENTS.with(|m| {
        let mut m = m.borrow_mut();
        m.steps += 1;
        if scan > adder { m.violations += 1; }
    });
    if trace_steps() {
        eprintln!(
            "MIDQ_P0_STEP dir={} step={i} q={} adder={adder} (M5 {adder_m} / D7 {adder_d}) scan={scan} (M1 {scan_m} / D {scan_d} / role {role_a} {role_b}) {}",
            if inverse { "bwd" } else { "fwd" },
            p.q.len(),
            if scan > adder { "VIOLATION" } else { "ok" }
        );
    }
}

pub(crate) fn report_moments(c: &Circuit) {
    eprintln!(
        "MIDQ_PACKED_TOFFOLI_SO_FAR ccx+ccz={} ops={} (at the end of this divide entry point)",
        toffoli_so_far(c),
        c.b.current_ops_len()
    );
    MOMENTS.with(|m| {
        let m = m.borrow();
        eprintln!(
            "MIDQ_P0_MOMENTS cut={} tail={} term_from={} substeps={} step_passes={} adder_max={} (step {}) scan_max={} ({} at step {}) role_max={} swap_max={} other_max={} ({}) planner_max={} ({}) steps_with_scan_above_adder={}{}",
            prefix_steps(), midq_tail_enabled(), terminal_from(),
            if m.real { "real" } else { "stubs" },
            m.steps, m.adder, m.adder_step, m.scan, m.scan_kind, m.scan_step, m.role, m.swap, m.other, m.other_kind, m.planner, m.planner_kind, m.violations,
            if m.real && !m.traced { " (census needs TRACE_PHASE_ACTIVE=1)" } else { "" }
        );
    });
}

/// Toffoli (CCX + CCZ) emitted so far (count-only and recording builders alike).
fn toffoli_so_far(c: &Circuit) -> usize {
    c.b.counted_kind_ops[OperationType::CCX as usize] + c.b.counted_kind_ops[OperationType::CCZ as usize]
}

fn trace_pz_steps() -> bool {
    std::env::var_os("MIDQ_TRACE_PZ_STEPS").is_some()
}

/// Print the cumulative per-direction Toffoli at the usual cuts
/// (`MIDQ_PZ_PREFIX <dir> cut=<k> emitted_toffoli=<T>`, the state machine's line).
fn report_prefix_toffoli(dir: &str, traced: &[usize]) {
    let steps = traced.len();
    for cut in [100usize, 250, 280, 320, 340, 360, 378, 380, 400, 420, 440, 480, 500, 530]
        .into_iter()
        .filter(|&cut| cut <= steps)
    {
        let toffoli: usize = traced[..cut].iter().sum();
        eprintln!("MIDQ_PZ_PREFIX {dir} cut={cut} emitted_toffoli={toffoli}");
    }
    let total: usize = traced.iter().sum();
    let max = traced.iter().copied().enumerate().max_by_key(|&(_, t)| t).unwrap_or((0, 0));
    eprintln!(
        "MIDQ_PZ_PREFIX {dir} steps={steps} emitted_toffoli={total} per_step_avg={} max={} (step {})",
        total.checked_div(steps).unwrap_or(0), max.1, max.0
    );
}

/// Forward row `i`: q to its envelope width, the popcount cache erased at
/// the first terminal-aware row, the step. Returns the row's Toffoli.
pub(super) fn forward_step(c: &mut Circuit, p: &mut Packed, i: usize) -> usize {
    let pop = popcount_on(&p.counter);
    let start = toffoli_so_far(c);
    let sec = c.push_section("pk.step");
    shrunken_pz_resize(c, &mut p.q, natural_q_width(i), "pk.q");
    if i > 0 {
        rebase_exponents(c, p, i - 1, i);
    }
    if i == terminal_from() && pop {
        prefix_popcount::from_quotient(c, &p.counter, &p.q, true);
    }
    pass_step(c, p, i, false);
    c.pop_section(&sec);
    toffoli_so_far(c) - start
}

/// Backward row `i` (the exact mirror of [`forward_step`]).
pub(super) fn backward_step(c: &mut Circuit, p: &mut Packed, i: usize) -> usize {
    let pop = popcount_on(&p.counter);
    let start = toffoli_so_far(c);
    let sec = c.push_section("pk.step");
    pass_step(c, p, i, true);
    if i == terminal_from() && pop {
        prefix_popcount::from_quotient(c, &p.counter, &p.q, false);
    }
    if i > 0 {
        rebase_exponents(c, p, i, i - 1);
        shrunken_pz_resize(c, &mut p.q, natural_q_width(i - 1), "pk.q");
    }
    c.pop_section(&sec);
    toffoli_so_far(c) - start
}

/// Forward prefix rows 0..steps with the per-step q envelope.
pub(super) fn prefix_forward(c: &mut Circuit, p: &mut Packed) {
    let steps = prefix_steps();
    let trace = trace_pz_steps();
    if dump_sched() {
        eprintln!("MIDQ_PACKED_SCHED steps={steps} term_from={} q_widths={:?}", terminal_from(), (0..steps).map(natural_q_width).collect::<Vec<_>>());
        for i in 0..steps {
            eprintln!("{}", super::sched::StepWidths::from_schedule(i).dump_line());
        }
    }
    let mut traced = Vec::with_capacity(steps);
    // MIDQ_EVAL_SHOTS (debug): checkpoint the data wires at S_0 and after every
    // forward row for trailmix_port::eval_shots (oracle comparison in the full circuit).
    let eval = crate::point_add::trailmix_port::eval_shots_enabled();
    let entry = if eval { crate::point_add::trailmix_port::eval_next_prefix_entry() } else { 0 };
    let pop = popcount_on(&p.counter);
    if eval {
        crate::point_add::trailmix_port::eval_mark(c, format!("entry {entry} S_0"), eval_data_ids(p), Some((entry, None, p.q.len(), p.counter.len(), pop)));
    }
    for i in 0..steps {
        let t = forward_step(c, p, i);
        if trace {
            eprintln!("MIDQ_PZ_STEP dir=fwd step={i} q={} toffoli={t}", p.q.len());
            traced.push(t);
        }
        if eval {
            crate::point_add::trailmix_port::eval_mark(c, format!("entry {entry} row {i}"), eval_data_ids(p), Some((entry, Some(i), p.q.len(), p.counter.len(), pop)));
        }
    }
    if trace {
        report_prefix_toffoli("forward", &traced);
    }
}

/// The data wires in `driver_selftest::data_ids` order (r1 | r2 | ex1 | ex2 |
/// q | counter | s_rot | off | parity) for the `MIDQ_EVAL_SHOTS` checkpoints.
fn eval_data_ids(p: &Packed) -> Vec<u64> {
    let mut ids: Vec<u64> = Vec::new();
    for reg in [&p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.counter, &p.s_rot] {
        ids.extend(reg.iter().map(|q| u64::from(q.id())));
    }
    ids.push(u64::from(p.off.as_ref().expect("off").id()));
    ids.push(u64::from(p.parity.as_deref().expect("parity").id()));
    ids
}

pub(super) fn prefix_backward(c: &mut Circuit, p: &mut Packed) {
    let steps = prefix_steps();
    let trace = trace_pz_steps();
    let mut traced = vec![0usize; steps];
    for i in (0..steps).rev() {
        let t = backward_step(c, p, i);
        if trace {
            eprintln!("MIDQ_PZ_STEP dir=bwd step={i} q={} toffoli={t}", p.q.len());
            traced[i] = t;
        }
    }
    if trace {
        report_prefix_toffoli("backward", &traced);
    }
}

// ---------------------------------------------------------------------------
// Handoff (cut 384 / 480): coefficients-first unpack, tail unchanged, repack
// ---------------------------------------------------------------------------

pub(crate) struct TailHandoff {
    a: Vec<QReg>,
    b: Vec<QReg>,
    ca: Vec<QReg>,
    cb: Vec<QReg>,
    state: MidqTailState,
    natural_q: usize,
}

/// Move `A` (LSB-anchored at R1[0..W0)) into a fresh `a`: `cswap(f_j, R1[j],
/// a[j])` under the thermometer `f_j = [j < e_A]` from the DFS engine on e_A.
fn unpack_value(c: &mut Circuit, ring: &[QReg], name: &str, w0: usize) -> Vec<QReg> {
    let a = c.alloc_qreg_bits(name, w0);
    let eng = take(c, "pk.eng", 8);
    for j in 0..w0 {
        c.cswap(&eng.0[7], &ring[j], &a[j]);
    }
    give(c, eng);
    a
}

fn repack_value(c: &mut Circuit, ring: &[QReg], a: Vec<QReg>) {
    let eng = take(c, "pk.eng", 8);
    for (j, q) in a.iter().enumerate() {
        c.cswap(&eng.0[7], &ring[j], q);
    }
    give(c, eng);
    for q in a { c.zero_and_free(q); }
}

fn handoff_forward(c: &mut Circuit, p: &mut Packed, passenger_carry_slot: &mut Option<QReg>) -> TailHandoff {
    let passenger_carry = passenger_carry_slot.as_ref();
    let sec = c.push_section("pk.unpack");
    let w0 = MIDQ_TAIL_VALUE_WIDTH[0] as usize;
    let cut = prefix_steps();
    // 0. Everything that is |0> at the cut goes first: the PZ step scratch
    //    (s_rot, off) and the q wires above MIDQ_HANDOFF_Q_BITS (the tail's
    //    own truncation, priced by tail_value_misses; moved ahead of the
    //    unpack so the value copies never coexist with them).
    if std::env::var("MIDQ_RELEASE_PZ_SCRATCH").ok().as_deref() == Some("1") {
        for bit in std::mem::take(&mut p.s_rot) { c.zero_and_free(bit); }
        c.zero_and_free(p.off.take().expect("packed offset scratch"));
    }
    let natural_q = p.q.len();
    if p.q.len() > midq_handoff_q_bits() {
        shrunken_pz_resize(c, &mut p.q, midq_handoff_q_bits(), "pk.q");
    }
    // 1. erase e_ca (M1-style aligned scan on R2), 2. erase e_cb (on R1).
    scan_stub(c, "unpack.eca", cut, true);
    for q in p.ex2.drain(EXP_BITS..) { c.zero_and_free(q); }
    scan_stub(c, "unpack.ecb", cut, true);
    for q in p.ex1.drain(EXP_BITS..) { c.zero_and_free(q); }
    // 3./4. a := A, erase e_A with bit_length_lean(a, dec).
    let (bv_cut, _) = exp_bases(cut - 1); // the frame of the last prefix row
    let a = unpack_value(c, &p.r1, "midq.a", w0);
    {
        let src: Vec<&QReg> = a.iter().collect();
        let e_a: Vec<QReg> = p.ex1.drain(..).collect();
        exp_scan(c, &src, &e_a, bv_cut, true, passenger_carry);
        for q in e_a { c.zero_and_free(q); }
    }
    // 5. b likewise, erase e_B.
    let b = unpack_value(c, &p.r2, "midq.b", w0);
    {
        let src: Vec<&QReg> = b.iter().collect();
        let e_b: Vec<QReg> = p.ex2.drain(..).collect();
        exp_scan(c, &src, &e_b, bv_cut, true, passenger_carry);
        for q in e_b { c.zero_and_free(q); }
    }
    // 6. ca := rev R2, cb := rev R1 (0 T).
    let mut ca: Vec<QReg> = std::mem::take(&mut p.r2).into_iter().rev().collect();
    let mut cb: Vec<QReg> = std::mem::take(&mut p.r1).into_iter().rev().collect();
    if payload_sign_loan::compact_padding() {
        if let Some(carry) = passenger_carry_slot.take() { c.zero_and_free(carry); }
    }
    c.pop_section(&sec);
    let (mut a, mut b) = (a, b);
    let state = midq_tail_forward_with_parity(
        c, &mut a, &mut b, &mut ca, &mut cb, &mut p.q, &mut p.counter, &mut p.parity,
    );
    TailHandoff { a, b, ca, cb, state, natural_q }
}

fn handoff_backward(c: &mut Circuit, p: &mut Packed, h: TailHandoff, passenger_carry_slot: &mut Option<QReg>, tag: &str) {
    let TailHandoff { mut a, mut b, mut ca, mut cb, state, natural_q } = h;
    midq_tail_backward_with_parity(
        c, &mut a, &mut b, &mut ca, &mut cb, &mut p.q, &mut p.counter, &mut p.parity, state,
    );
    let sec = c.push_section("pk.repack");
    if payload_sign_loan::compact_padding() && lowq_borrow_passenger_carry_enabled()
        && passenger_carry_slot.is_none() {
        *passenger_carry_slot = Some(c.alloc_qreg("midq.restored.passenger_carry"));
    }
    let passenger_carry = passenger_carry_slot.as_ref();
    let cut = prefix_steps();
    assert_eq!(ca.len(), RING);
    assert_eq!(cb.len(), RING);
    p.r2 = ca.into_iter().rev().collect();
    p.r1 = cb.into_iter().rev().collect();
    let (bv_cut, _) = exp_bases(cut - 1);
    // 5'. e_B := bl(b); b back into R2.
    p.ex2 = c.alloc_qreg_bits(&format!("{tag}.eB"), EXP_BITS);
    {
        let src: Vec<&QReg> = b.iter().collect();
        exp_scan(c, &src, &p.ex2, bv_cut, false, passenger_carry);
    }
    repack_value(c, &p.r2, b);
    // 3'/4'. e_A := bl(a); a back into R1.
    p.ex1 = c.alloc_qreg_bits(&format!("{tag}.eA"), EXP_BITS);
    {
        let src: Vec<&QReg> = a.iter().collect();
        exp_scan(c, &src, &p.ex1, bv_cut, false, passenger_carry);
    }
    repack_value(c, &p.r1, a);
    // 2'/1'. e_cb, e_ca by the aligned scans.
    p.ex1.extend(c.alloc_qreg_bits(&format!("{tag}.ecb"), EXP_BITS));
    scan_stub(c, "repack.ecb", cut, true);
    p.ex2.extend(c.alloc_qreg_bits(&format!("{tag}.eca"), EXP_BITS));
    scan_stub(c, "repack.eca", cut, true);
    // 0'. q back to its natural envelope width; the PZ step scratch.
    shrunken_pz_resize(c, &mut p.q, natural_q, "pk.q");
    if p.off.is_none() {
        p.s_rot = c.alloc_qreg_bits(&format!("{tag}.srot"), trailmix_srot_width());
        p.off = Some(c.alloc_qreg(&format!("{tag}.off")));
    }
    c.pop_section(&sec);
}

// ---------------------------------------------------------------------------
// The two divide entry points (mirrors of shrunken_pz_divide_forward/_cancel)
// ---------------------------------------------------------------------------

fn half_bytes() -> Vec<u8> {
    vec![
        0x18, 0xfe, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x00,
    ]
}

// In S_0 parity is the known constant 1. Store sign XOR parity on that
// existing wire; the walk only XORs swap decisions into it. After the inverse
// walk the original sign is recoverable and parity can be reset to 1.
fn fold_input_sign(c: &mut Circuit, p: &Packed, sign: QReg) {
    let parity = p.parity.as_deref().expect("live parity");
    c.cx(&sign, parity);
    c.x(&sign);
    c.cx(parity, &sign);
    c.zero_and_free(sign);
}

fn unfold_input_sign(c: &mut Circuit, p: &Packed) -> QReg {
    let parity = p.parity.as_deref().expect("live parity");
    let sign = c.alloc_qreg("pk.restored.input_sign");
    c.x(&sign);
    c.cx(parity, &sign);
    c.cx(&sign, parity);
    sign
}

fn prefix_recycle_carry(c: &mut Circuit, p: &mut Packed, carry: &mut Option<QReg>, inverse: bool) {
    // The passenger is untouched throughout a prefix walk. Its canonical
    // overflow is only borrowed by the scans at the two endpoints.
    let restore = carry.is_some();
    if let Some(q) = carry.take() { c.zero_and_free(q); }
    if inverse { prefix_backward(c, p); } else { prefix_forward(c, p); }
    if restore { *carry = Some(c.alloc_qreg("pk.restored.passenger_carry")); }
}

pub(crate) fn divide_forward(
    c: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    use crate::point_add::trailmix_port::arith::rfold_mbu::mod_mul_rfold_mbu;
    assert_eq!(dx.len(), 257);
    assert_eq!(dy.len(), 257);
    let compact_passenger = midq_tail_enabled() && payload_sign_loan::compact_padding();
    if compact_passenger && !lowq_borrow_passenger_carry_enabled() {
        payload_sign_loan::park_padding(c, &mut dy);
    }
    let mut passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("dy has a canonical zero overflow bit"));
    let half = half_bytes();
    let sgn = c.alloc_qreg("shpzdiv.sgn");
    compare_geq_const(c, &dx, &half, &sgn);
    controlled_field_neg(c, &sgn, &dx);

    let mut p = enter_s0(c, dx, passenger_carry.as_ref(), "pk");
    let mut input_sign = Some(sgn);
    if !midq_tail_enabled() { fold_input_sign(c, &p, input_sign.take().unwrap()); }
    prefix_recycle_carry(c, &mut p, &mut passenger_carry, false);

    if midq_tail_enabled() {
        let sgn = input_sign.take().unwrap();
        let h = handoff_forward(c, &mut p, &mut passenger_carry);
        if let Some(carry) = passenger_carry.take() { dy.push(carry); }
        let mut payload_sign = Some(sgn);
        let sign_loaned = payload_sign_loan::begin(c, &mut dy, &mut payload_sign);
        let mut lambda = c.alloc_qreg_bits("shpzdiv.lambda", 257);
        mod_mul_rfold_mbu(c, &lambda, &h.ca, &dy);
        midq_field_neg(c, payload_sign_loan::control(&dy, &payload_sign), &lambda, &h.ca);
        payload_sign_loan::finish(&mut dy, &mut payload_sign, sign_loaned);
        let sgn = payload_sign.take().expect("sign restored before multiplier ghosting");
        let mut ghosts = Vec::with_capacity(dy.len());
        for q in &dy { ghosts.push(c.hmr_ghost(q)); }
        for q in dy { c.zero_and_free(q); }
        if compact_passenger {
            payload_sign_loan::park_signed_high(c, &mut lambda, &sgn);
        } else {
            passenger_carry = lowq_borrow_passenger_carry_enabled()
                .then(|| lambda.pop().expect("lambda has a canonical zero overflow bit"));
        }
        handoff_backward(c, &mut p, h, &mut passenger_carry, "pk.restored");
        prefix_backward(c, &mut p);
        let mut dx = exit_s0(c, p, passenger_carry.as_ref());
        report_moments(c);
        shrunken_pz_resize(c, &mut dx, 257, "dx");
        if compact_passenger {
            if let Some(carry) = passenger_carry.take() { c.zero_and_free(carry); }
            payload_sign_loan::restore_signed_high(c, &mut lambda, &sgn);
        }
        controlled_field_neg(c, &sgn, &dx);
        compare_geq_const(c, &dx, &half, &sgn);
        c.zero_and_free(sgn);
        if let Some(carry) = passenger_carry.take() { lambda.push(carry); }
        let dy_new = c.alloc_qreg_bits("shpzdiv.dy", 257);
        mod_mul_rfold_mbu(c, &dy_new, &lambda[..257], &dx);
        for (g, q) in ghosts.into_iter().zip(dy_new.iter()) { c.resolve_ghost(g, q); }
        return (dx, dy_new, lambda);
    }

    // --- cut 530: teardown, lambda = dy * cb, ghost dy, re-create, backward ---
    let cb = teardown_530(c, &mut p, passenger_carry.as_ref());
    if let Some(carry) = passenger_carry.take() { dy.push(carry); }
    let mut lambda = c.alloc_qreg_bits("shpzdiv.lambda", 257);
    mod_mul_rfold_mbu(c, &lambda, &cb[..257], &dy);
    let f = c.alloc_qreg("shpzdiv.negf");
    c.cx(p.parity.as_deref().expect("live parity"), &f);
    c.x(&f);
    controlled_field_neg(c, &f, &lambda);
    c.x(&f);
    c.cx(p.parity.as_deref().expect("live parity"), &f);
    c.zero_and_free(f);
    let mut ghosts = Vec::with_capacity(dy.len());
    for q in &dy { ghosts.push(c.hmr_ghost(q)); }
    for q in dy { c.zero_and_free(q); }
    passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| lambda.pop().expect("lambda has a canonical zero overflow bit"));
    recreate_530(c, &mut p, cb, passenger_carry.as_ref(), "pk.re");
    prefix_recycle_carry(c, &mut p, &mut passenger_carry, true);
    let sgn = unfold_input_sign(c, &p);
    let mut dx = exit_s0(c, p, passenger_carry.as_ref());
    report_moments(c);
    shrunken_pz_resize(c, &mut dx, 257, "dx");
    controlled_field_neg(c, &sgn, &dx);
    compare_geq_const(c, &dx, &half, &sgn);
    c.zero_and_free(sgn);
    if let Some(carry) = passenger_carry.take() { lambda.push(carry); }
    let dy_new = c.alloc_qreg_bits("shpzdiv.dy", 257);
    mod_mul_rfold_mbu(c, &dy_new, &lambda[..257], &dx);
    for (g, q) in ghosts.into_iter().zip(dy_new.iter()) { c.resolve_ghost(g, q); }
    (dx, dy_new, lambda)
}

pub(crate) fn divide_cancel(
    c: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
    lambda: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    use crate::point_add::trailmix_port::arith::rfold_mbu::{mod_mul_rfold_mbu, mod_mul_rfold_mbu_undo};
    assert_eq!(dx.len(), 257);
    assert_eq!(dy.len(), 257);
    assert_eq!(lambda.len(), 257);
    let compact_passenger = midq_tail_enabled() && payload_sign_loan::compact_padding();
    if compact_passenger && !lowq_borrow_passenger_carry_enabled() {
        payload_sign_loan::park_padding(c, &mut dy);
    }
    let mut passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("new_dy has a canonical zero overflow bit"));
    let half = half_bytes();
    let sgn = c.alloc_qreg("shpzcan.sgn");
    compare_geq_const(c, &dx, &half, &sgn);
    controlled_field_neg(c, &sgn, &dx);
    let mut lam_ghosts = Vec::with_capacity(lambda.len());
    for q in &lambda { lam_ghosts.push(c.hmr_ghost(q)); }
    for q in lambda { c.zero_and_free(q); }

    let mut p = enter_s0(c, dx, passenger_carry.as_ref(), "pkc");
    let mut input_sign = Some(sgn);
    if !midq_tail_enabled() { fold_input_sign(c, &p, input_sign.take().unwrap()); }
    prefix_recycle_carry(c, &mut p, &mut passenger_carry, false);

    if midq_tail_enabled() {
        let sgn = input_sign.take().unwrap();
        let h = handoff_forward(c, &mut p, &mut passenger_carry);
        if let Some(carry) = passenger_carry.take() { dy.push(carry); }
        let mut payload_sign = Some(sgn);
        let sign_loaned = payload_sign_loan::begin(c, &mut dy, &mut payload_sign);
        let temp = c.alloc_qreg_bits("shpzcan.temp", 257);
        mod_mul_rfold_mbu(c, &temp, &h.ca, &dy);
        midq_field_neg(c, payload_sign_loan::control(&dy, &payload_sign), &temp, &h.ca);
        for (g, q) in lam_ghosts.into_iter().zip(temp.iter()) { c.resolve_ghost(g, q); }
        midq_field_neg(c, payload_sign_loan::control(&dy, &payload_sign), &temp, &h.ca);
        mod_mul_rfold_mbu_undo(c, &temp, &h.ca, &dy);
        payload_sign_loan::finish(&mut dy, &mut payload_sign, sign_loaned);
        let sgn = payload_sign.take().expect("sign restored before reverse PZ");
        for q in temp { c.zero_and_free(q); }
        if sign_loaned && !compact_passenger {
            dy.push(c.alloc_qreg("shpzcan.restored.dy.high"));
        }
        passenger_carry = (lowq_borrow_passenger_carry_enabled() && !compact_passenger)
            .then(|| dy.pop().expect("new_dy has a restored zero overflow bit"));
        handoff_backward(c, &mut p, h, &mut passenger_carry, "pkc.restored");
        prefix_backward(c, &mut p);
        let mut dx = exit_s0(c, p, passenger_carry.as_ref());
        report_moments(c);
        shrunken_pz_resize(c, &mut dx, 257, "dx");
        controlled_field_neg(c, &sgn, &dx);
        compare_geq_const(c, &dx, &half, &sgn);
        c.zero_and_free(sgn);
        if let Some(carry) = passenger_carry.take() { dy.push(carry); }
        if compact_passenger && dy.len() == 256 {
            dy.push(c.alloc_qreg("midq.passenger.restored_padding"));
        }
        return (dx, dy);
    }

    let cb = teardown_530(c, &mut p, passenger_carry.as_ref());
    if let Some(carry) = passenger_carry.take() { dy.push(carry); }
    let temp = c.alloc_qreg_bits("shpzcan.temp", 257);
    mod_mul_rfold_mbu(c, &temp, &cb[..257], &dy);
    let f = c.alloc_qreg("shpzcan.negf");
    c.cx(p.parity.as_deref().expect("live parity"), &f);
    c.x(&f);
    controlled_field_neg(c, &f, &temp);
    for (g, q) in lam_ghosts.into_iter().zip(temp.iter()) { c.resolve_ghost(g, q); }
    controlled_field_neg(c, &f, &temp);
    c.x(&f);
    c.cx(p.parity.as_deref().expect("live parity"), &f);
    c.zero_and_free(f);
    mod_mul_rfold_mbu_undo(c, &temp, &cb[..257], &dy);
    for q in temp { c.zero_and_free(q); }
    passenger_carry = lowq_borrow_passenger_carry_enabled()
        .then(|| dy.pop().expect("new_dy has a restored zero overflow bit"));
    recreate_530(c, &mut p, cb, passenger_carry.as_ref(), "pkc.re");
    prefix_recycle_carry(c, &mut p, &mut passenger_carry, true);
    let sgn = unfold_input_sign(c, &p);
    let mut dx = exit_s0(c, p, passenger_carry.as_ref());
    report_moments(c);
    shrunken_pz_resize(c, &mut dx, 257, "dx");
    controlled_field_neg(c, &sgn, &dx);
    compare_geq_const(c, &dx, &half, &sgn);
    c.zero_and_free(sgn);
    if let Some(carry) = passenger_carry.take() { dy.push(carry); }
    (dx, dy)
}
