//! Selftest of `masked_add_refs` (`masked_add.rs` module doc), included from
//! there via `#[path]`. Every case is checked against the classical field
//! model (value of the field, foreign bits, captures), phase 0, every freed
//! ancilla 0, the address / flag wires restored, then the gate-reversed
//! sequence (coherent variants) and the X-bracket twin (`subtract` flipped,
//! same captures) are run on the outputs and must restore the inputs.
//!
//! Sizes: widths 1-3 and 8-10 exhaustive over target x addend x boundary x
//! ctrl; 11-16 exhaustive over boundary x ctrl with random operands; 257 wide
//! with random operands (foreign bits above the boundary in both registers)
//! for the D7/M5-shaped zones. Mask kinds: per-cell flags, the local coherent
//! reference DFS engine (T-accounted per leaf), `onehot_stream` coherent
//! (T-accounted) and `onehot_stream` with its default measured clears.
//! `MIDQ_PACKED_MASKED_ADD_QUICK=1` skips the width-10 exhaustive sweep.

use std::cell::Cell;

use super::{masked_add_refs, Captures, ZoneMask};
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::packed::onehot_stream::onehot_stream_with;
use crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::predicate_clear_selftest::checked_apply;
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const LIMBS: usize = 5; // 320 bits >= 257 + 1

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Bits([u64; LIMBS]);

impl Bits {
    fn zero() -> Self {
        Bits([0; LIMBS])
    }
    fn from_u64(v: u64) -> Self {
        let mut b = Self::zero();
        b.0[0] = v;
        b
    }
    fn get(&self, j: usize) -> bool {
        (self.0[j / 64] >> (j % 64)) & 1 == 1
    }
    fn set(&mut self, j: usize, v: bool) {
        if v {
            self.0[j / 64] |= 1u64 << (j % 64);
        } else {
            self.0[j / 64] &= !(1u64 << (j % 64));
        }
    }
    fn random(n: usize, rng: &mut Xorshift) -> Self {
        let mut b = Self::zero();
        for j in 0..n {
            b.set(j, rng.bit());
        }
        b
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Case {
    target: Bits,
    addend: Bits,
    e: usize,
    ctrl: bool,
    ov: bool,
}

struct Xorshift(u64);

impl Xorshift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn bit(&mut self) -> bool {
        self.next() >> 63 == 1
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MaskKind {
    /// `ZoneMask::Flags`: one caller flag per zone cell.
    Flags,
    /// `ZoneMask::Sweep` on the local coherent reference DFS engine.
    RefSweep,
    /// `ZoneMask::Sweep` on `onehot_stream_with(.., coherent = true, ..)`.
    ExponentCoherent,
    /// `ZoneMask::Exponent`: `onehot_stream` with its default clears.
    Exponent,
    /// `ZoneMask::Rebased`: a 7-bit register holding `E - base` with
    /// `base = min(zone_lo, n - 127)` (the driver's rule for a ring top `n`),
    /// `onehot_stream` with its default clears.
    Rebased,
}

impl MaskKind {
    fn name(self) -> &'static str {
        match self {
            MaskKind::Flags => "flags",
            MaskKind::RefSweep => "ref-dfs",
            MaskKind::ExponentCoherent => "onehot_stream(coherent)",
            MaskKind::Exponent => "onehot_stream",
            MaskKind::Rebased => "onehot_stream(rebased 7-bit)",
        }
    }
    fn coherent(self) -> bool {
        !matches!(self, MaskKind::Exponent | MaskKind::Rebased)
    }
}

#[derive(Clone, Copy, Debug)]
struct Variant {
    n: usize,
    zone_lo: usize,
    subtract: bool,
    captures: bool,
    mask: MaskKind,
}

impl Variant {
    /// The exponent base of the `Rebased` kind (0 otherwise).
    fn base(&self) -> usize {
        if self.mask == MaskKind::Rebased { self.n.saturating_sub(127).min(self.zone_lo) } else { 0 }
    }
    /// Width of the exponent register.
    fn exp_bits(&self) -> usize {
        if self.mask == MaskKind::Rebased {
            let span = self.n - self.base(); // register values [0, span]
            ((usize::BITS - span.leading_zeros()) as usize).max(7)
        } else {
            addr_width(self.n)
        }
    }
    /// The largest boundary the register can hold (`n` unless rebased and clipped).
    fn e_max(&self) -> usize {
        if self.mask == MaskKind::Rebased { self.n.min(self.base() + (1usize << self.exp_bits()) - 1) } else { self.n }
    }
}

struct Built {
    v: Variant,
    ops: Vec<Op>,
    nq: usize,
    nb: usize,
    ctrl: QubitId,
    target: Vec<QubitId>,
    addend: Vec<QubitId>,
    ov: Option<QubitId>,
    exp: Vec<QubitId>,
    flags: Vec<QubitId>,
    t_total: usize,
    /// CCX inside the leaf bodies (cells + captures); RefSweep / ExponentCoherent only.
    t_leaf: Option<usize>,
    peak: u32,
    data_wires: u32,
}

fn count_t(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

/// Bits needed to hold every boundary `0..=n`; the design's 9-bit exponent
/// register for the wide (D7/M5-shaped) cases so the engine's wire count is
/// the design's.
fn addr_width(n: usize) -> usize {
    let minimal = (usize::BITS - n.leading_zeros()) as usize;
    if n >= 64 { minimal.max(9) } else { minimal }
}

/// Test-only coherent reference one-hot engine: prefix-AND DFS over `exp`
/// (little-endian) rooted at `root`, leaves `[lo, hi)` in ascending or
/// descending order, `body(c, i, g_i)` with `g_i = root AND [exp == i]`.
/// 2 T per visited internal node, CCX uncomputes, no measurement.
fn ref_onehot(
    c: &mut Circuit,
    root: &QReg,
    exp: &[QReg],
    lo: usize,
    hi: usize,
    descending: bool,
    body: &mut dyn FnMut(&mut Circuit, usize, &QReg),
) {
    #[allow(clippy::too_many_arguments)]
    fn visit(
        c: &mut Circuit,
        parent: &QReg,
        exp: &[QReg],
        level: usize,
        base: usize,
        lo: usize,
        hi: usize,
        descending: bool,
        body: &mut dyn FnMut(&mut Circuit, usize, &QReg),
    ) {
        let span = 1usize << level;
        if base >= hi || base + span <= lo {
            return;
        }
        if level == 0 {
            body(c, base, parent);
            return;
        }
        let bit = &exp[level - 1];
        let half = span / 2;
        let child = c.alloc_qreg("madd.test.node");
        c.ccx(parent, bit, &child); // parent AND bit
        let order = if descending { [true, false] } else { [false, true] };
        for upper in order {
            if upper {
                visit(c, &child, exp, level - 1, base + half, lo, hi, descending, body);
            } else {
                c.cx(parent, &child); // parent AND NOT bit
                visit(c, &child, exp, level - 1, base, lo, hi, descending, body);
                c.cx(parent, &child);
            }
        }
        c.ccx(parent, bit, &child);
        c.zero_and_free(child);
    }
    assert!(hi <= 1usize << exp.len());
    visit(c, root, exp, exp.len(), 0, lo, hi, descending, body);
}

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}

fn build(v: Variant) -> Built {
    let n = v.n;
    let z = n - v.zone_lo;
    let mut c = Circuit::new();
    let ctrl = c.alloc_qreg("madd.test.ctrl");
    let target = c.alloc_qreg_bits("madd.test.a", n);
    let addend = c.alloc_qreg_bits("madd.test.b", n);
    let ov = v.captures.then(|| c.alloc_qreg("madd.test.ov"));
    let exp = match v.mask {
        MaskKind::Flags => Vec::new(),
        _ => c.alloc_qreg_bits("madd.test.e", v.exp_bits()),
    };
    let flags = match v.mask {
        MaskKind::Flags => c.alloc_qreg_bits("madd.test.f", z),
        _ => Vec::new(),
    };
    let data_wires = c.b.active_qubits;
    let t_refs: Vec<&QReg> = target.iter().collect();
    let b_refs: Vec<&QReg> = addend.iter().collect();
    let f_refs: Vec<&QReg> = flags.iter().collect();
    let captures = Captures { overflow: ov.as_ref(), absorb: v.captures };
    let leaf_t = Cell::new(0usize);
    let zone = v.zone_lo..n;
    match v.mask {
        MaskKind::Flags => masked_add_refs(
            &mut c, &ctrl, &t_refs, &b_refs, zone, ZoneMask::Flags(&f_refs), v.subtract, captures,
        ),
        MaskKind::Exponent => masked_add_refs(
            &mut c, &ctrl, &t_refs, &b_refs, zone, ZoneMask::Exponent(&exp), v.subtract, captures,
        ),
        MaskKind::Rebased => masked_add_refs(
            &mut c, &ctrl, &t_refs, &b_refs, zone, ZoneMask::Rebased(&exp, v.base()), v.subtract, captures,
        ),
        MaskKind::RefSweep | MaskKind::ExponentCoherent => {
            let (lo, hi) = (v.zone_lo, n);
            let use_ref = v.mask == MaskKind::RefSweep;
            let mut driver = |c: &mut Circuit,
                              descending: bool,
                              body: &mut dyn FnMut(&mut Circuit, usize, &QReg)| {
                let mut counted = |c: &mut Circuit, i: usize, g: &QReg| {
                    let start = c.b.ops.len();
                    body(c, i, g);
                    leaf_t.set(leaf_t.get() + count_t(&c.b.ops[start..]));
                };
                if use_ref {
                    ref_onehot(c, &ctrl, &exp, lo, hi, descending, &mut counted);
                } else {
                    onehot_stream_with(c, &exp, lo, hi, Some(&ctrl), descending, true, &mut counted);
                }
            };
            masked_add_refs(
                &mut c, &ctrl, &t_refs, &b_refs, zone, ZoneMask::Sweep(&mut driver), v.subtract, captures,
            );
        }
    }
    let ops = c.b.ops.clone();
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let all: Vec<QubitId> = ids(&target)
        .into_iter()
        .chain(ids(&addend))
        .chain(ids(&exp))
        .chain(ids(&flags))
        .chain(ov.iter().map(|q| QubitId(q.id().into())))
        .chain([QubitId(ctrl.id().into())])
        .collect();
    let nq = (nq as usize).max(all.iter().map(|q| q.0 as usize + 1).max().unwrap());
    let t_total = count_t(&ops);
    let t_leaf = matches!(v.mask, MaskKind::RefSweep | MaskKind::ExponentCoherent).then(|| leaf_t.get());
    Built {
        v,
        nq,
        nb: nb as usize,
        ctrl: QubitId(ctrl.id().into()),
        target: ids(&target),
        addend: ids(&addend),
        ov: ov.as_ref().map(|q| QubitId(q.id().into())),
        exp: ids(&exp),
        flags: ids(&flags),
        t_total,
        t_leaf,
        peak: c.b.peak_qubits,
        data_wires,
        ops,
    }
}

/// The classical field model of the module doc.
fn model(v: &Variant, case: &Case) -> Case {
    let mut out = *case;
    if !case.ctrl {
        return out;
    }
    let mut carry = false;
    for j in 0..case.e {
        let a = case.target.get(j);
        let b = case.addend.get(j);
        let (s, c_out) = if v.subtract {
            (a ^ b ^ carry, (!a & b) | (!(a ^ b) & carry))
        } else {
            (a ^ b ^ carry, (a & b) | ((a ^ b) & carry))
        };
        out.target.set(j, s);
        carry = c_out;
    }
    if v.captures && case.e < v.n {
        out.ov ^= carry;
        out.target.set(case.e, case.target.get(case.e) ^ carry);
    }
    out
}

/// Run one batch (<= 64 cases) of `ops` on the wires of `b`; returns the read
/// back cases; asserts phase 0, address/flag wires restored, ancillae clean.
fn run_batch<R: XofReader>(b: &Built, ops: &[Op], cases: &[Case], rng: &mut R) -> Vec<Case> {
    let n = b.v.n;
    let mask = u64::MAX >> (64 - cases.len());
    let mut sim = Simulator::new(b.nq, b.nb + 1, rng);
    for (s, case) in cases.iter().enumerate() {
        let bit = 1u64 << s;
        if case.ctrl {
            *sim.qubit_mut(b.ctrl) |= bit;
        }
        for j in 0..n {
            if case.target.get(j) {
                *sim.qubit_mut(b.target[j]) |= bit;
            }
            if case.addend.get(j) {
                *sim.qubit_mut(b.addend[j]) |= bit;
            }
        }
        if let Some(ov) = b.ov {
            if case.ov {
                *sim.qubit_mut(ov) |= bit;
            }
        }
        let e_reg = case.e.checked_sub(b.v.base()).expect("boundary below the exponent base");
        for (k, &id) in b.exp.iter().enumerate() {
            if (e_reg >> k) & 1 == 1 {
                *sim.qubit_mut(id) |= bit;
            }
        }
        for (k, &id) in b.flags.iter().enumerate() {
            if b.v.zone_lo + k < case.e {
                *sim.qubit_mut(id) |= bit;
            }
        }
    }
    checked_apply(&mut sim, ops, mask);
    assert_eq!(sim.phase & mask, 0, "phase mismatch ({:?})", b.v);
    let mut out = Vec::with_capacity(cases.len());
    for (s, case) in cases.iter().enumerate() {
        let read = |id: QubitId| (sim.qubit(id) >> s) & 1 == 1;
        let mut o = *case;
        o.ctrl = read(b.ctrl);
        for j in 0..n {
            o.target.set(j, read(b.target[j]));
            o.addend.set(j, read(b.addend[j]));
        }
        if let Some(ov) = b.ov {
            o.ov = read(ov);
        }
        if !b.exp.is_empty() {
            let e: usize = b.exp.iter().enumerate().map(|(k, &id)| (read(id) as usize) << k).sum();
            assert_eq!(e + b.v.base(), case.e, "exponent changed ({:?})", b.v);
        }
        for (k, &id) in b.flags.iter().enumerate() {
            assert_eq!(read(id), b.v.zone_lo + k < case.e, "flag changed ({:?})", b.v);
        }
        out.push(o);
    }
    for &id in b.target.iter().chain(&b.addend).chain(&b.exp).chain(&b.flags).chain(&b.ov).chain([&b.ctrl]) {
        *sim.qubit_mut(id) = 0;
    }
    for (i, &q) in sim.qubits.iter().enumerate() {
        assert_eq!(q & mask, 0, "dirty ancilla qubit {i} ({:?})", b.v);
    }
    out
}

struct Harness {
    fwd: Built,
    twin: Built,
    rev: Vec<Op>,
    checked: usize,
    /// Skip the gate-reversed run (the big exhaustive sweeps: it is exact by
    /// construction for a coherent circuit; the X-bracket twin is the design's inverse).
    skip_reversed: bool,
}

impl Harness {
    fn new(v: Variant) -> Self {
        let fwd = build(v);
        let twin = build(Variant { subtract: !v.subtract, ..v });
        let rev: Vec<Op> = fwd.ops.iter().rev().cloned().collect();
        Self { fwd, twin, rev, checked: 0, skip_reversed: false }
    }

    fn check_batch<R: XofReader>(&mut self, batch: &[Case], rng: &mut R) {
        let v = self.fwd.v;
        let reversed = v.mask.coherent() && !self.skip_reversed;
        let got = run_batch(&self.fwd, &self.fwd.ops, batch, rng);
        for (case, out) in batch.iter().zip(&got) {
            let want = model(&v, case);
            assert_eq!(
                *out, want,
                "masked_add_refs value mismatch: {v:?} e={} ctrl={} target={:?} addend={:?}",
                case.e, case.ctrl, case.target, case.addend
            );
        }
        if reversed {
            let back = run_batch(&self.fwd, &self.rev, &got, rng);
            assert_eq!(back, batch, "gate-reversed inverse failed: {v:?}");
        }
        let back = run_batch(&self.twin, &self.twin.ops, &got, rng);
        assert_eq!(back, batch, "X-bracket twin inverse failed: {v:?}");
        self.checked += batch.len();
    }

    fn check_all<R: XofReader>(&mut self, cases: impl Iterator<Item = Case>, rng: &mut R) {
        let mut batch = Vec::with_capacity(64);
        for case in cases {
            batch.push(case);
            if batch.len() == 64 {
                self.check_batch(&batch, rng);
                batch.clear();
            }
        }
        if !batch.is_empty() {
            self.check_batch(&batch, rng);
        }
    }
}

fn exhaustive(v: Variant) -> impl Iterator<Item = Case> {
    let n = v.n;
    let span = 1u64 << n;
    (0..span).flat_map(move |t| {
        (0..span).flat_map(move |b| {
            (v.zone_lo..=n).flat_map(move |e| {
                [false, true].into_iter().map(move |ctrl| Case {
                    target: Bits::from_u64(t),
                    addend: Bits::from_u64(b),
                    e,
                    ctrl,
                    ov: (t ^ b ^ e as u64) & 1 == 1,
                })
            })
        })
    })
}

fn random_cases(v: Variant, per_boundary: usize, seed: u64) -> Vec<Case> {
    let mut rng = Xorshift(seed | 1);
    let mut cases = Vec::new();
    for e in v.zone_lo..=v.n {
        for ctrl in [false, true] {
            for _ in 0..per_boundary {
                cases.push(Case {
                    target: Bits::random(v.n, &mut rng),
                    addend: Bits::random(v.n, &mut rng),
                    e,
                    ctrl,
                    ov: rng.bit(),
                });
            }
        }
    }
    cases
}

fn wide_cases(v: Variant, count: usize, seed: u64) -> Vec<Case> {
    let mut rng = Xorshift(seed | 1);
    (0..count)
        .map(|i| {
            let e = match i % 4 {
                0 => v.zone_lo,
                1 => v.n,
                _ => v.zone_lo + rng.below(v.n - v.zone_lo + 1),
            }
            .min(v.e_max());
            Case {
                target: Bits::random(v.n, &mut rng),
                addend: Bits::random(v.n, &mut rng),
                e,
                ctrl: i % 8 != 3,
                ov: rng.bit(),
            }
        })
        .collect()
}

fn report(b: &Built) {
    let v = b.v;
    let z = v.n - v.zone_lo;
    let plain = 3 * v.zone_lo;
    let cells = 9 * z;
    let caps = if v.captures { 2 * z } else { 0 };
    match b.t_leaf {
        Some(leaf) => {
            assert_eq!(leaf, cells + caps, "leaf T per masked cell ({v:?})");
            let engine = b.t_total - plain - leaf;
            eprintln!(
                "PACKED_MASKED_ADD T n={} zone=[{},{}) subtract={} captures={} mask={}: total={} = plain {}x3 + masked {}x9 (MAJ 4 + UMA 5) + captures {}x{} + engine (2 sweeps) {}; peak ancillae {} (c, t, f + engine)",
                v.n, v.zone_lo, v.n, v.subtract as u8, v.captures as u8, v.mask.name(), b.t_total,
                v.zone_lo, z, if v.captures { 2 } else { 0 }, z, engine, b.peak - b.data_wires
            );
        }
        None => {
            if z == 0 || v.mask == MaskKind::Flags {
                assert_eq!(b.t_total, plain + cells, "T of the sweep-free variant ({v:?})");
            }
            eprintln!(
                "PACKED_MASKED_ADD T n={} zone=[{},{}) subtract={} captures={} mask={}: total={} (plain {}x3, masked {}x9, captures {}x{}, engine {}); peak ancillae {}",
                v.n, v.zone_lo, v.n, v.subtract as u8, v.captures as u8, v.mask.name(), b.t_total,
                v.zone_lo, z, if v.captures { 2 } else { 0 }, z,
                b.t_total as isize - (plain + cells + caps) as isize, b.peak - b.data_wires
            );
        }
    }
}

// ===========================================================================
// Adversarial review additions (2026-09-13): the refuters' classes of
// tools/spike/packed_design.md (tight packing gap 0 = cb's MSB adjacent to the
// field end, e_A = W_A with off = 0 = A's bit 0 adjacent, the first multiply
// with ca_old = 0 and e_B in [226, 256], all-zero windows, foreign bits
// adjacent to the field end, maximum amounts, inverse on the same data) on
// synthetic extremes and on REAL packed states from the pz_prefix recurrence
// of tools/packed_prefix_model.py (run here in U512: every division row is a
// D7 case in the s-frame, every multiply row an M5 case in the ring rotated
// up by s2, each with the end-to-end expectation [A_new | gap | cb] /
// [B | gap | ca_new] of the design, not only the primitive's field model),
// the documented width-miss behaviour (E outside [zone.start, n]: every zone
// cell adds, no capture, ancillae still clean), and the design's section-4
// unit-cost model printed next to the measured T.
// ===========================================================================

use ruint::aliases::U512;
use std::collections::BTreeMap;

const RING: usize = 257;
const NSTEPS: usize = 530;
const NINPUTS: usize = 64;

impl Bits {
    fn ones(lo: usize, hi: usize) -> Self {
        let mut b = Self::zero();
        for j in lo..hi {
            b.set(j, true);
        }
        b
    }
    fn or(self, o: Bits) -> Bits {
        let mut r = self;
        for i in 0..LIMBS {
            r.0[i] |= o.0[i];
        }
        r
    }
}

fn p_secp() -> U512 {
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
    /// ca AFTER the step's multiply (the R2 content at D7).
    ca: U512,
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
    cb: U512,
    s2: usize,
    ca_new: U512,
}

/// Per-step sample envelopes (the schedule's W_A / W_c over the sampled inputs).
struct Envelope {
    w_a: Vec<usize>,
    w_c: Vec<usize>,
}

/// Verbatim `pz_prefix` (tools/packed_prefix_model.py) with row recording and
/// the per-step envelope of the pre-step state (`W_A = max(bl A, bl B)`,
/// `W_c = max(bl ca, bl cb, bl ca_post)`).
fn trace(x_orig: U512, div: &mut Vec<DivRow>, mul: &mut Vec<MulRow>, env: &mut Envelope) {
    let p = p_secp();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let one = U512::from(1u64);
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, one, U512::ZERO);
    for step in 0..NSTEPS {
        assert!(a * cb + b * (ca + q * cb) == p, "row invariant");
        assert!(bl(&a) + bl(&cb) <= RING && bl(&b) + bl(&ca) <= RING, "packing invariant");
        env.w_a[step] = env.w_a[step].max(bl(&a)).max(bl(&b));
        env.w_c[step] = env.w_c[step].max(bl(&ca)).max(bl(&cb));
        if a.is_zero() && b == one && q.is_zero() {
            continue;
        }
        if a < b && !q.is_zero() {
            let s2 = q.trailing_zeros();
            let ca_new = ca + (cb << s2);
            mul.push(MulRow { step, a, b, ca_old: ca, cb, s2, ca_new });
            q ^= one << s2;
            ca = ca_new;
            env.w_c[step] = env.w_c[step].max(bl(&ca));
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
                    div.push(DivRow { step, a_old: a, b, ca, cb, s, off, a_new });
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
    assert!(a.is_zero() && q.is_zero(), "input did not terminate by {NSTEPS}");
}

fn sample_rows() -> (Vec<DivRow>, Vec<MulRow>, Envelope) {
    let mut seed = Shake256::default();
    seed.update(b"packed-masked-add-review-inputs-v1");
    let mut xof = seed.finalize_xof();
    let p = p_secp();
    let mut div = Vec::new();
    let mut mul = Vec::new();
    let mut env = Envelope { w_a: vec![0; NSTEPS], w_c: vec![0; NSTEPS] };
    for _ in 0..NINPUTS {
        let mut bytes = [0u8; 64];
        xof.read(&mut bytes[..32]);
        let x = U512::from_le_bytes(bytes) % p;
        let x = if x.is_zero() { U512::from(1u64) } else { x };
        trace(x, &mut div, &mut mul, &mut env);
    }
    (div, mul, env)
}

/// LSB-frame ring content: value bit w at wire w, coefficient bit i at wire 256 - i.
fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

/// D7's window of a division row: R1 in the s-frame (the LSB frame
/// `[A_old | gap | cb]` rotated DOWN by s on `[0, W_A)`), R2 in the LSB frame,
/// and the s-frame of the design's post-state `[A_new | gap | cb]` as the
/// end-to-end expectation. Field `[0, E)`, `E = e_B + off`.
fn d7_window(row: &DivRow, w_a: usize) -> (Bits, Bits, Bits) {
    let r1 = ring_lsb(&row.a_old, &row.cb);
    let r2 = ring_lsb(&row.b, &row.ca);
    let r1_new = ring_lsb(&row.a_new, &row.cb);
    let (mut target, mut addend, mut want) = (Bits::zero(), Bits::zero(), Bits::zero());
    for w in 0..w_a {
        target.set(w, r1[(w + row.s) % w_a]);
        addend.set(w, r2[w]);
        want.set(w, r1_new[(w + row.s) % w_a]);
    }
    (target, addend, want)
}

/// M5's window of a multiply row: R2 on the ring `[256 - W_c, 257)` rotated UP
/// by s2 (ca >> s2 in the field, ca's low s2 bits at the ring bottom, B's
/// in-ring bits shifted up), R1 in the LSB frame, cell j = wire 256 - j, and
/// the same rotation of the design's post-state `[B | gap | ca_new]` as the
/// end-to-end expectation; the carry out of the field is
/// `[bl(ca_new) == e_cb + s2 + 1]`. Field `[0, e_cb)`.
fn m5_window(row: &MulRow, w_c: usize) -> (Bits, Bits, Bits, bool) {
    let n = w_c + 1;
    let base = RING - 1 - w_c;
    let r2 = ring_lsb(&row.b, &row.ca_old);
    let r1 = ring_lsb(&row.a, &row.cb);
    let r2_new = ring_lsb(&row.b, &row.ca_new);
    let rot = |src: &[bool], r: usize| src[base + (r + n - row.s2 % n) % n];
    let (mut target, mut addend, mut want) = (Bits::zero(), Bits::zero(), Bits::zero());
    for j in 0..n {
        let r = w_c - j;
        target.set(j, rot(&r2, r));
        addend.set(j, r1[RING - 1 - j]);
        want.set(j, rot(&r2_new, r));
    }
    let carry = bl(&row.ca_new) == bl(&row.cb) + row.s2 + 1;
    (target, addend, want, carry)
}

/// A real-state case: the primitive's inputs plus the design-level expectation
/// (target after, and the carry-out that the capture must XOR into `ov`).
#[derive(Clone, Copy)]
struct RealCase {
    case: Case,
    want_target: Bits,
    want_carry: bool,
}

type GroupKey = (usize, usize, bool, bool, u8);

fn mask_of(k: u8) -> MaskKind {
    match k {
        0 => MaskKind::Exponent,
        1 => MaskKind::ExponentCoherent,
        _ => MaskKind::RefSweep,
    }
}

/// Run every group: first the classical check that the primitive's field model
/// composed with the layout gives the design's post-state (no borrow in D7,
/// the absorb wire a gap zero or B's top bit with carry 0 in M5, ...), then
/// the circuit against the field model, phase 0, ancillae clean, both inverses.
fn run_real_groups<R: XofReader>(
    what: &str,
    groups: &BTreeMap<GroupKey, Vec<RealCase>>,
    rng: &mut R,
    checked: &mut usize,
    variants: &mut usize,
) {
    for (&(n, zone_lo, subtract, captures, mk), rows) in groups {
        let v = Variant { n, zone_lo, subtract, captures, mask: mask_of(mk) };
        for rc in rows {
            let m = model(&v, &rc.case);
            let want_t = if rc.case.ctrl { rc.want_target } else { rc.case.target };
            assert_eq!(
                m.target, want_t,
                "{what}: the field model does not give the design's post-state ({v:?} e={} ctrl={})",
                rc.case.e, rc.case.ctrl
            );
            let want_ov = rc.case.ov ^ (rc.case.ctrl && captures && rc.case.e < n && rc.want_carry);
            assert_eq!(m.ov, want_ov, "{what}: captured carry differs from the design's ({v:?} e={})", rc.case.e);
        }
        let mut h = Harness::new(v);
        h.check_all(rows.iter().map(|rc| rc.case), rng);
        *checked += h.checked;
        *variants += 1;
    }
}

/// Synthetic extremes for one (n, zone) shape: all-zero windows, maximum
/// amounts (field all ones + all ones, carry / borrow through the whole
/// field), the carry out of the top cell only, foreign bits adjacent to the
/// field end (target[E], addend[E], every bit above E) in both registers,
/// whole-window ones; E at the zone edge, one above it, the middle, n - 1
/// (the last leaf) and n (no toggle leaf); both ctrl values.
fn extreme_cases(v: Variant, rng: &mut Xorshift) -> Vec<Case> {
    let (n, lo) = (v.n, v.zone_lo);
    let mut es = vec![lo, lo + 1, (lo + n) / 2, n.saturating_sub(1), n];
    es.retain(|&e| e >= lo && e <= n);
    es.sort_unstable();
    es.dedup();
    let mut cases = Vec::new();
    for e in es {
        let field = Bits::ones(0, e);
        let above = Bits::ones(e, n);
        let bit_e = if e < n { Bits::ones(e, e + 1) } else { Bits::zero() };
        let msb = if e > 0 { Bits::ones(e - 1, e) } else { Bits::zero() };
        let one = if e > 0 { Bits::ones(0, 1) } else { Bits::zero() };
        let mut rnd_field = || {
            let mut b = Bits::random(n, rng);
            for j in e..n {
                b.set(j, false);
            }
            b
        };
        let ra = rnd_field();
        let rb = rnd_field();
        let pats: [(Bits, Bits); 16] = [
            (Bits::zero(), Bits::zero()),
            (field, field),
            (field.or(above), field.or(above)),
            (field, one),
            (field.or(above), one),
            (Bits::zero(), field),
            (above, field.or(above)),
            (bit_e, bit_e),
            (bit_e, above),
            (msb.or(bit_e), msb),
            (msb, msb.or(above)),
            (ra.or(above), rb.or(above)),
            (ra, rb.or(above)),
            (Bits::ones(0, n), Bits::ones(0, n)),
            (Bits::zero(), Bits::ones(0, n)),
            (Bits::ones(0, n), Bits::zero()),
        ];
        for (k, (t, b)) in pats.into_iter().enumerate() {
            for ctrl in [false, true] {
                cases.push(Case { target: t, addend: b, e, ctrl, ov: (k + e) % 2 == 1 });
            }
        }
    }
    cases
}

/// The documented width-miss behaviour of the sweep kinds: with E below
/// zone.start (the toggle leaf is never visited) or above n (no leaf in the
/// window) the thermometer stays 1, every cell adds, no capture fires - i.e.
/// the circuit acts as E = n - and the ancillae are still clean, phase 0, the
/// twin and the gate-reversed sequence still invert it.
fn check_miss_batch<R: XofReader>(h: &mut Harness, batch: &[Case], rng: &mut R) {
    let v = h.fwd.v;
    let got = run_batch(&h.fwd, &h.fwd.ops, batch, rng);
    for (case, out) in batch.iter().zip(&got) {
        let mut want = model(&v, &Case { e: v.n, ..*case });
        want.e = case.e;
        assert_eq!(*out, want, "width-miss behaviour (E outside [zone.start, n]) differs from 'E = n': {v:?} e={}", case.e);
    }
    if v.mask.coherent() {
        let back = run_batch(&h.fwd, &h.rev, &got, rng);
        assert_eq!(back, batch, "gate-reversed inverse failed on a width miss: {v:?}");
    }
    let back = run_batch(&h.twin, &h.twin.ops, &got, rng);
    assert_eq!(back, batch, "X-bracket twin inverse failed on a width miss: {v:?}");
    h.checked += batch.len();
}

fn miss_cases(v: Variant, k: usize, rng: &mut Xorshift) -> Vec<Case> {
    let (n, lo) = (v.n, v.zone_lo);
    let mut es = vec![0, lo / 2, lo.saturating_sub(1), n + 1, (1usize << k) - 1];
    es.retain(|&e| e < lo || (e > n && e < (1usize << k)));
    es.sort_unstable();
    es.dedup();
    let mut cases = Vec::new();
    for e in es {
        let pats = [
            (Bits::zero(), Bits::zero()),
            (Bits::ones(0, n), Bits::ones(0, n)),
            (Bits::random(n, rng), Bits::random(n, rng)),
            (Bits::ones(0, e.min(n)), Bits::ones(0, e.min(n))),
        ];
        for (t, b) in pats {
            for ctrl in [false, true] {
                cases.push(Case { target: t, addend: b, e, ctrl, ov: rng.bit() });
            }
        }
    }
    cases
}

/// The design's section-4 unit costs for one shape: 3 T per plain cell, 3 + 6
/// per zone cell (coherent t), two engine sweeps at 1.0 T per visited leaf,
/// 1 T per capture per leaf.
fn design_model(v: Variant) -> usize {
    let z = v.n - v.zone_lo;
    3 * v.n + 6 * z + if z > 0 { 2 * z } else { 0 } + if v.captures { 2 * z } else { 0 }
}

fn report_design(b: &Built, label: &str) {
    let v = b.v;
    let z = v.n - v.zone_lo;
    let design = design_model(v);
    let cells = 3 * v.zone_lo + 9 * z + if v.captures { 2 * z } else { 0 };
    let engine = b.t_total as isize - cells as isize;
    eprintln!(
        "PACKED_MASKED_ADD design-4 {label}: n={} z={} subtract={} captures={} mask={}: measured {} vs design {} (delta {:+}; cells {} = design's exactly, engine {} = {:.2} T/leaf/sweep vs design 1.0); peak ancillae {}",
        v.n, z, v.subtract as u8, v.captures as u8, v.mask.name(), b.t_total, design,
        b.t_total as isize - design as isize, cells, engine,
        if z > 0 { engine as f64 / (2.0 * z as f64) } else { 0.0 }, b.peak - b.data_wires
    );
    assert_eq!(b.t_total - engine as usize, cells, "cell T of {label}");
    if z > 0 && v.mask != MaskKind::Flags {
        // The engine's overhead over 1 T per leaf per sweep (2 T coherent) is the
        // folded root's quadrant moves (<= ~14 T per sweep for a 9-bit address,
        // onehot_stream doc).
        let per_leaf = if matches!(v.mask, MaskKind::Exponent | MaskKind::Rebased) { 2 } else { 4 };
        assert!(engine as usize <= per_leaf * (z + 20), "engine T of {label}: {engine} for z={z}");
    }
}

fn run_adversarial<R: XofReader>(rng: &mut R, checked: &mut usize, variants: &mut usize) {
    let started = std::time::Instant::now();
    let mut xs = Xorshift(0x5851_f42d_4c95_7f2d);

    // (1) Synthetic extremes on the D7 / M5 shapes and a small one, every
    //     subtract / capture setting, both sweep engines (+ flags without captures).
    let mut extreme = 0usize;
    for (n, zone_lo) in [(16usize, 5usize), (76, 1), (257, 181), (257, 0), (257, 233), (257, 256)] {
        for mask in [MaskKind::Exponent, MaskKind::ExponentCoherent, MaskKind::Flags] {
            for subtract in [false, true] {
                for captures in [false, true] {
                    if captures && mask == MaskKind::Flags {
                        continue;
                    }
                    let v = Variant { n, zone_lo, subtract, captures, mask };
                    let mut h = Harness::new(v);
                    let cases = extreme_cases(v, &mut xs);
                    h.check_all(cases.into_iter(), rng);
                    extreme += h.checked;
                    *checked += h.checked;
                    *variants += 1;
                }
            }
        }
    }

    // (2) Documented width-miss behaviour (E < zone.start, E > n) on the sweep kinds.
    let mut miss = 0usize;
    for (n, zone_lo) in [(16usize, 8usize), (76, 1), (257, 181), (257, 233)] {
        for mask in [MaskKind::Exponent, MaskKind::ExponentCoherent] {
            for subtract in [false, true] {
                for captures in [false, true] {
                    let v = Variant { n, zone_lo, subtract, captures, mask };
                    let mut h = Harness::new(v);
                    let cases = miss_cases(v, addr_width(n), &mut xs);
                    for batch in cases.chunks(64) {
                        check_miss_batch(&mut h, batch, rng);
                    }
                    miss += h.checked;
                    *checked += h.checked;
                    *variants += 1;
                }
            }
        }
    }

    // (3) Real packed states: every division row -> D7, every multiply row -> M5.
    let (div, mul, env) = sample_rows();
    let lo_a = |w_a: usize| w_a.saturating_sub(78);

    // (3a) D7 rows grouped by the sample envelope of their step (the schedule's
    //      zone `[max(lo_A, 257 - W_c), W_A)`): supported rows (E >= zone.start)
    //      against the design's post-state; rows below the zone's lower edge are
    //      support misses (counted, and checked for the documented behaviour).
    let mut d7_env: BTreeMap<GroupKey, Vec<RealCase>> = BTreeMap::new();
    let mut d7_env_miss: BTreeMap<GroupKey, Vec<Case>> = BTreeMap::new();
    let (mut d7_rows, mut d7_miss_rows, mut d7_gap0, mut d7_off1, mut d7_term, mut d7_e_eq_n, mut d7_ea_top_off0) = (0, 0, 0, 0, 0, 0, 0);
    for (i, row) in div.iter().enumerate() {
        let (e_a, e_b, e_cb) = (bl(&row.a_old), bl(&row.b), bl(&row.cb));
        let e = e_b + row.off as usize;
        let w_a = env.w_a[row.step];
        let w_c = env.w_c[row.step];
        assert!(w_a >= e_a && w_a <= 256);
        let zone_lo = lo_a(w_a).max(RING.saturating_sub(w_c)).min(w_a);
        let (target, addend, want) = d7_window(row, w_a);
        let ctrl = i % 8 != 5;
        let case = Case { target, addend, e, ctrl, ov: i % 3 == 1 };
        d7_rows += 1;
        d7_gap0 += (RING - e_a - e_cb == 0 && w_a > e_a) as usize; // cb's MSB is the s-frame wire E
        d7_off1 += row.off as usize;
        d7_term += row.a_new.is_zero() as usize;
        d7_e_eq_n += (e == w_a) as usize;
        d7_ea_top_off0 += (e_a == w_a && !row.off) as usize;
        // Alternate the engine and the capture setting by step parity: D7 has no
        // captures; running them anyway checks "no borrow out of the field" on
        // real rows (the captured borrow must be 0, the absorb a no-op).
        let mk = (row.step % 2) as u8;
        let captures = mk == 1;
        if e >= zone_lo {
            d7_env.entry((w_a, zone_lo, true, captures, mk)).or_default().push(RealCase { case, want_target: want, want_carry: false });
        } else {
            d7_miss_rows += 1;
            d7_env_miss.entry((w_a, zone_lo, true, captures, mk)).or_default().push(case);
        }
    }
    run_real_groups("D7 envelope", &d7_env, rng, checked, variants);
    for (&(n, zone_lo, subtract, captures, mk), cases) in &d7_env_miss {
        let v = Variant { n, zone_lo, subtract, captures, mask: mask_of(mk) };
        let mut h = Harness::new(v);
        for batch in cases.chunks(64) {
            check_miss_batch(&mut h, batch, rng);
        }
        miss += h.checked;
        *checked += h.checked;
        *variants += 1;
    }

    // (3b) D7 rows with the TIGHT window W_A = e_A (A's bit 0 is the first
    //      wire above the field when off = 0; cb's MSB is when the R1 gap is 0)
    //      and the zone edge at E, one below E, or 78 below (clipped to 0):
    //      a circuit per (W_A, zone edge), so a bounded class sample.
    let mut d7_tight: BTreeMap<GroupKey, Vec<RealCase>> = BTreeMap::new();
    let mut d7_classes = [0usize; 5];
    let class_cap = 96usize;
    for (i, row) in div.iter().enumerate() {
        let (e_a, e_b, e_cb) = (bl(&row.a_old), bl(&row.b), bl(&row.cb));
        let e = e_b + row.off as usize;
        let class = if RING - e_a - e_cb == 0 {
            0 // gap 0: cb's MSB at wire E of the s-frame
        } else if row.a_new.is_zero() {
            1 // terminal division (B = 1)
        } else if row.off {
            2 // off = 1: the operand at cell e_B is R2's spare gap zero
        } else if row.s == 0 {
            3 // s = 0: E = e_A = W_A, no zone (plain adder)
        } else {
            4 // off = 0, A's bit 0 at wire E
        };
        if d7_classes[class] >= class_cap {
            continue;
        }
        d7_classes[class] += 1;
        // W_A = e_A: A's bit 0 is the s-frame wire E (the first wire above the
        // field) for both off values. Gap-0 rows take W_A = e_A + 1 so that cb's
        // MSB (LSB-frame wire e_A) is inside the ring and lands at wire E, with
        // A's bit 0 at E + 1.
        let w_a = if class == 0 { (e_a + 1).min(RING) } else { e_a };
        let zone_lo = match i % 3 {
            0 => e,
            1 => e.saturating_sub(1),
            _ => e.saturating_sub(78),
        }
        .min(w_a);
        let (target, addend, want) = d7_window(row, w_a);
        let case = Case { target, addend, e, ctrl: i % 8 != 5, ov: i % 3 == 1 };
        let mk = ((i / 3) % 2) as u8;
        d7_tight.entry((w_a, zone_lo, true, mk == 1, mk)).or_default().push(RealCase { case, want_target: want, want_carry: false });
    }
    run_real_groups("D7 tight", &d7_tight, rng, checked, variants);

    // (3c) M5 rows grouped by the sample envelope: window = the M3 ring
    //      `[256 - W_c, 257)` (W_c + 1 cells), zone cells `[257 - W_A, W_c + 1)`
    //      (empty when W_A <= 256 - W_c), captures = absorb + carry, E = e_cb.
    let mut m5_env: BTreeMap<GroupKey, Vec<RealCase>> = BTreeMap::new();
    let mut m5_env_miss: BTreeMap<GroupKey, Vec<Case>> = BTreeMap::new();
    let (mut m5_rows, mut m5_miss_rows, mut m5_first, mut m5_first_hi, mut m5_tightb, mut m5_carry, mut m5_drain, mut m5_nozone) = (0, 0, 0, 0, 0, 0, 0, 0);
    for (i, row) in mul.iter().enumerate() {
        let (e_b, e_cb) = (bl(&row.b), bl(&row.cb));
        let w_a = env.w_a[row.step];
        let w_c = env.w_c[row.step];
        assert!(w_c >= bl(&row.ca_new) && w_c >= e_cb && w_c <= 256);
        let n = w_c + 1;
        let zone_lo = if w_a > 256 - w_c { RING - w_a } else { n };
        let (target, addend, want, carry) = m5_window(row, w_c);
        let case = Case { target, addend, e: e_cb, ctrl: i % 8 != 5, ov: i % 3 == 1 };
        m5_rows += 1;
        m5_first += row.ca_old.is_zero() as usize;
        m5_first_hi += (row.ca_old.is_zero() && e_b >= 226) as usize;
        m5_tightb += (e_b + row.s2 + e_cb == RING) as usize;
        m5_carry += carry as usize;
        m5_drain += row.a.is_zero() as usize;
        m5_nozone += (zone_lo == n) as usize;
        if e_b + row.s2 + e_cb == RING {
            assert!(!carry, "tight multiply row with carry = 1 (design fact violated)");
        }
        let mk = (row.step % 2) as u8;
        if e_cb >= zone_lo {
            m5_env.entry((n, zone_lo, false, true, mk)).or_default().push(RealCase { case, want_target: want, want_carry: carry });
        } else {
            m5_miss_rows += 1;
            m5_env_miss.entry((n, zone_lo, false, true, mk)).or_default().push(case);
        }
    }
    run_real_groups("M5 envelope", &m5_env, rng, checked, variants);
    for (&(n, zone_lo, subtract, captures, mk), cases) in &m5_env_miss {
        let v = Variant { n, zone_lo, subtract, captures, mask: mask_of(mk) };
        let mut h = Harness::new(v);
        for batch in cases.chunks(64) {
            check_miss_batch(&mut h, batch, rng);
        }
        miss += h.checked;
        *checked += h.checked;
        *variants += 1;
    }

    // (3d) M5 rows with the TIGHT ring W_c = max(bl ca_old, bl cb, bl ca_new)
    //      and the zone edge at E (= 257 - W_A with W_A = 257 - e_cb, the
    //      smallest supported value), one below, or 78 below.
    let mut m5_tight: BTreeMap<GroupKey, Vec<RealCase>> = BTreeMap::new();
    let mut m5_classes = [0usize; 5];
    for (i, row) in mul.iter().enumerate() {
        let (e_b, e_cb) = (bl(&row.b), bl(&row.cb));
        let class = if row.ca_old.is_zero() && e_b >= 226 {
            0 // first multiply, B's low bits wrap into the M1 window (refuter 2)
        } else if row.ca_old.is_zero() {
            1 // first multiply, e_B <= 225
        } else if e_b + row.s2 + e_cb == RING {
            2 // tight: the absorb wire is B's top bit (carry provably 0)
        } else if row.a.is_zero() {
            3 // draining row (A = 0, B = 1)
        } else {
            4
        };
        if m5_classes[class] >= class_cap {
            continue;
        }
        m5_classes[class] += 1;
        let w_c = bl(&row.ca_old).max(e_cb).max(bl(&row.ca_new));
        let n = w_c + 1;
        let zone_lo = match i % 3 {
            0 => e_cb,
            1 => e_cb.saturating_sub(1),
            _ => e_cb.saturating_sub(78),
        };
        let (target, addend, want, carry) = m5_window(row, w_c);
        let case = Case { target, addend, e: e_cb, ctrl: i % 8 != 5, ov: i % 3 == 1 };
        let mk = ((i / 3) % 2) as u8;
        m5_tight.entry((n, zone_lo, false, true, mk)).or_default().push(RealCase { case, want_target: want, want_carry: carry });
    }
    run_real_groups("M5 tight", &m5_tight, rng, checked, variants);

    eprintln!(
        "PACKED_MASKED_ADD adversarial: extremes {extreme} cases; width-miss behaviour {miss} cases; real states {NINPUTS} inputs x {NSTEPS} steps: D7 rows {d7_rows} (envelope-supported {}, below the envelope zone {d7_miss_rows}; gap1=0 with cb's MSB at wire E {d7_gap0}, off=1 {d7_off1}, terminal {d7_term}, E=n {d7_e_eq_n}, e_A=W_A&off=0 {d7_ea_top_off0}; tight-window sample per class [gap0, terminal, off1, s0, off0] {:?}), M5 rows {m5_rows} (envelope-supported {}, below the envelope zone {m5_miss_rows}, no zone at the step {m5_nozone}; first multiply {m5_first} [e_B>=226: {m5_first_hi}], tight absorb-on-B {m5_tightb}, carry=1 {m5_carry}, draining {m5_drain}; tight-ring sample per class [first&e_B>=226, first, tightB, draining, other] {:?}); groups {} in {:.1}s",
        d7_rows - d7_miss_rows,
        d7_classes,
        m5_rows - m5_miss_rows,
        m5_classes,
        d7_env.len() + d7_env_miss.len() + d7_tight.len() + m5_env.len() + m5_env_miss.len() + m5_tight.len(),
        started.elapsed().as_secs_f64()
    );
}

pub(super) fn run() {
    let quick = std::env::var("MIDQ_PACKED_MASKED_ADD_QUICK").ok().as_deref() == Some("1");
    let started = std::time::Instant::now();
    let mut hash = Shake256::default();
    hash.update(b"packed-masked-add-v1");
    let mut rng = hash.finalize_xof();
    let mut checked = 0usize;
    let mut variants = 0usize;
    let all_masks = [MaskKind::Flags, MaskKind::RefSweep, MaskKind::ExponentCoherent, MaskKind::Exponent];

    // Widths 1-3 and 8: exhaustive, every mask kind, subtract, captures, three zone edges.
    for n in [1usize, 2, 3, 8] {
        let lows: Vec<usize> = if n == 8 { vec![0, 3, 8] } else { vec![0, n / 2, n] };
        for zone_lo in lows {
            for mask in all_masks {
                if n == 8 && zone_lo != 3 && !matches!(mask, MaskKind::Flags | MaskKind::Exponent) {
                    continue;
                }
                for subtract in [false, true] {
                    for captures in [false, true] {
                        if captures && mask == MaskKind::Flags {
                            continue;
                        }
                        let v = Variant { n, zone_lo, subtract, captures, mask };
                        let mut h = Harness::new(v);
                        h.check_all(exhaustive(v), &mut rng);
                        checked += h.checked;
                        variants += 1;
                        if n == 8 && zone_lo == 3 && subtract == captures {
                            report(&h.fwd);
                        }
                    }
                }
            }
        }
    }

    // Width 9: exhaustive on the sweep engines with captures; width 10 on the reference engine.
    for (n, masks) in [(9usize, vec![MaskKind::RefSweep, MaskKind::ExponentCoherent]), (10, vec![MaskKind::RefSweep])] {
        if n == 10 && quick {
            continue;
        }
        for mask in masks {
            for subtract in [false, true] {
                if n == 10 && subtract {
                    continue;
                }
                let v = Variant { n, zone_lo: 3, subtract, captures: true, mask };
                let mut h = Harness::new(v);
                h.skip_reversed = true;
                h.check_all(exhaustive(v), &mut rng);
                checked += h.checked;
                variants += 1;
            }
        }
    }

    // Widths 11-16: exhaustive over boundary x ctrl, random operands (foreign bits above E).
    for n in 11usize..=16 {
        for mask in all_masks {
            for subtract in [false, true] {
                let captures = mask != MaskKind::Flags;
                let v = Variant { n, zone_lo: n / 3, subtract, captures, mask };
                let mut h = Harness::new(v);
                let cases = random_cases(v, 24, 0x9e37_79b9_7f4a_7c15 ^ (n as u64) << 8 ^ mask as u64);
                h.check_all(cases.into_iter(), &mut rng);
                checked += h.checked;
                variants += 1;
            }
        }
    }

    // 257 wide = M5's window at step 378 (W_c + 1 cells, zone cells [257 - W_A, W_c + 1)
    // = [181, 257), z_c = 76); zone edges 0 (all masked), 181 (M5 @378), 233 (M5 @480).
    for zone_lo in [0usize, 181, 233] {
        for mask in all_masks.iter().copied().chain([MaskKind::Rebased]) {
            for subtract in [false, true] {
                for captures in [false, true] {
                    if captures && mask == MaskKind::Flags {
                        continue;
                    }
                    let v = Variant { n: 257, zone_lo, subtract, captures, mask };
                    let mut h = Harness::new(v);
                    let cases = wide_cases(v, 256, 0xd1b5_4a32_d192_ed03 ^ (zone_lo as u64) << 4 ^ mask as u64);
                    h.check_all(cases.into_iter(), &mut rng);
                    checked += h.checked;
                    variants += 1;
                    if zone_lo == 181 && !subtract && (captures || mask == MaskKind::Flags) {
                        report(&h.fwd);
                    }
                }
            }
        }
    }
    // D7 at step 378: window W_A = 76 cells, zone [max(lo_A, 257 - W_c), W_A) = [1, 76)
    // (75 masked), subtract, no captures, 9-bit exponent (and the 7-bit rebased register).
    for mask in [MaskKind::ExponentCoherent, MaskKind::Exponent, MaskKind::Rebased] {
        let v = Variant { n: 76, zone_lo: 1, subtract: true, captures: false, mask };
        let mut h = Harness::new(v);
        let cases = wide_cases(v, 256, 0x2545_f491_4f6c_dd1d ^ mask as u64);
        h.check_all(cases.into_iter(), &mut rng);
        checked += h.checked;
        variants += 1;
        report(&h.fwd);
    }

    // The design's section-4 unit costs next to the measured T on the two
    // consumer shapes at step 378 (M5: 257 cells, zone 76, carry + absorb;
    // D7: 76 cells, zone 75, subtract) and at step 480 (M5 zone 24, D7 24/23).
    for (v, label) in [
        (Variant { n: 257, zone_lo: 181, subtract: false, captures: true, mask: MaskKind::Exponent }, "M5 @378"),
        (Variant { n: 257, zone_lo: 181, subtract: false, captures: true, mask: MaskKind::Rebased }, "M5 @378 rebased 7-bit (base 130)"),
        (Variant { n: 76, zone_lo: 1, subtract: true, captures: false, mask: MaskKind::Rebased }, "D7 @378 rebased 7-bit (base 0)"),
        (Variant { n: 216, zone_lo: 139, subtract: true, captures: false, mask: MaskKind::Rebased }, "D7 @100 rebased 7-bit (base 89)"),
        (Variant { n: 257, zone_lo: 181, subtract: false, captures: true, mask: MaskKind::ExponentCoherent }, "M5 @378 coherent engine"),
        (Variant { n: 76, zone_lo: 1, subtract: true, captures: false, mask: MaskKind::Exponent }, "D7 @378"),
        (Variant { n: 76, zone_lo: 1, subtract: true, captures: false, mask: MaskKind::ExponentCoherent }, "D7 @378 coherent engine"),
        (Variant { n: 257, zone_lo: 233, subtract: false, captures: true, mask: MaskKind::Exponent }, "M5 @480"),
        (Variant { n: 24, zone_lo: 1, subtract: true, captures: false, mask: MaskKind::Exponent }, "D7 @480"),
        (Variant { n: 257, zone_lo: 0, subtract: false, captures: true, mask: MaskKind::Exponent }, "M5 all-masked"),
    ] {
        report_design(&build(v), label);
    }

    run_adversarial(&mut rng, &mut checked, &mut variants);

    eprintln!(
        "PACKED_MASKED_ADD selftest: PASS ({checked} cases over {variants} variants in {:.1}s; value, foreign bits, phase, ancillae, gate-reversed inverse, X-bracket twin; adversarial extremes, width-miss behaviour, real D7/M5 states)",
        started.elapsed().as_secs_f64()
    );
}
