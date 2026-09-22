//! Selftest for `capture_compare` (included by `capture_compare.rs`).
//!
//! * widths 8-12: exhaustive over (v, u) with the capture position sweeping the
//!   whole window (root = 1); widths 8-9: exhaustive over the full input word
//!   (v, u, every address value incl. off-window ones, root, out) for six
//!   window shapes (both `FieldEnd` forms, sub-windows, `k = 0` addresses);
//! * 78-wide cascades with 9-bit addresses (the D4/D9/M10 and role shapes,
//!   windows inside one top quarter and straddling two), random operands;
//! * 257-wide cascades, random operands with FOREIGN bits above the capture
//!   position (the witness must be the low-k compare) and a tie variant (bits
//!   above the field equal: the witness is then also the full compare);
//! * every case: witness correct, operands/address/root unchanged, phase 0,
//!   every reset hits a zero wire, every ancilla zero at the end, and the
//!   primitive applied a second time restores the input exactly (self-inverse);
//! * measurement outcomes forced all-0 / all-1 / 0x55 / random; the coherent
//!   (`MIDQ_ONEHOT_COHERENT=1`) and unfolded (`MIDQ_ONEHOT_NOFOLD=1`) engines.
//!
//! Review additions (adversarial cases, 2026-09-13):
//!
//! * a Toffoli model asserted on EVERY built circuit: `T = 2n + z + engine`,
//!   `engine = visited internal tree nodes + 3 per visited top quarter`
//!   (doubled with coherent clears), which pins the deviation from the
//!   design's `2n + 2z` unit cost to the engine's boundary nodes and the fold;
//! * synthetic edge patterns on 257-wide cascades with the widest legal
//!   windows (z = 257) for every k in 1..=257: all-zero / all-one operands,
//!   ties with every (v[k], u[k]) combination adjacent to the field end,
//!   decided fields whose adjacent foreign bits would flip a full compare,
//!   single-bit fields, the longest carry chains (2^(k-1) - 1 vs 2^(k-1)),
//!   root = 0, `out` = 1, off-window and out-of-address-space addresses,
//!   k = 0 and k = 257, and a window whose `hi` is clamped; all four
//!   measurement modes;
//! * real states: `tools/packed_prefix_model.py::pz_prefix` ported (192
//!   inputs x 530 steps, 64 inputs = the 64 shots of one batch per step),
//!   laid out on the rings for every consumer shape and checked against the
//!   model's own predicate: role compute `[A < B]` at the step start (capture
//!   at `257 - max(e_ca, e_cb)`, precondition asserted), role clear
//!   `[ca < cb]` at the step end (capture at `257 - max(e_A, e_B)`), D4
//!   `[(A >> s_raw) < B]` in the rotated frame (tight ring `e_A = W_A` and the
//!   batch envelope, R1 gap 0 on half the rows), D9 `[~B < R]` after the
//!   subtract (witness = off_old), M10 `[(ca_new >> D) < cb]` on the
//!   coefficient ring rotated by `D = s2 + carry` (witness = carry; first
//!   multiplies with `ca_old = 0` and `e_B >= 226`, B's bits inside the M3
//!   ring, the absorb wire holding B's top bit), inactive rows with root = 0,
//!   draining and frozen rows; the exact full-ring forms and the design's
//!   thin 78-wide windows from the batch envelope (residue and width misses
//!   counted); the same sections again under both engine variants.

use super::{capture_compare, CaptureWindow, FieldEnd};
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

const MAX_N: usize = 257;

struct Measurements {
    forced: Option<u8>,
    random: sha3::Shake256Reader,
}

impl Measurements {
    fn new(mode: usize, label: &str) -> Self {
        let mut hash = Shake256::default();
        hash.update(b"packed-capture-compare-v1");
        hash.update(label.as_bytes());
        hash.update(&(mode as u64).to_le_bytes());
        Self { forced: [Some(0), Some(255), Some(0x55), None][mode], random: hash.finalize_xof() }
    }
}

impl XofReader for Measurements {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(byte) = self.forced { out.fill(byte); } else { self.random.read(out); }
    }
}

/// A built circuit. Data qubits in the order v[0..n), u[0..n), addr[0..m), root, out.
struct Case {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    is_data: Vec<bool>,
    n: usize,
    m: usize,
    window: CaptureWindow,
    nq: usize,
    nb: usize,
    toffoli: usize,
    ancilla: usize,
    carry_room: usize,
}

impl Case {
    fn build(n: usize, m: usize, window: CaptureWindow) -> Case {
        assert!(n <= MAX_N);
        let mut c = Circuit::new();
        let v = c.alloc_qreg_bits("test.v", n);
        let u = c.alloc_qreg_bits("test.u", n);
        let addr = c.alloc_qreg_bits("test.addr", m);
        let root = c.alloc_qreg("test.root");
        let out = c.alloc_qreg("test.out");
        let vr: Vec<&QReg> = v.iter().collect();
        let ur: Vec<&QReg> = u.iter().collect();
        let carry_room = super::super::sched::scratch_room(&mut c)
            .saturating_sub(1 + super::carry::engine_room(m));
        let carry_room = std::env::var("MIDQ_CAPTURE_CHUNK_ROOM").ok()
            .and_then(|v| v.parse::<usize>().ok()).map_or(carry_room, |v| v.min(carry_room));
        capture_compare(&mut c, &root, &vr, &ur, &addr, window, &out);
        let ids: Vec<QubitId> = v.iter().chain(&u).chain(&addr).chain([&root, &out])
            .map(|q| QubitId(q.id().into())).collect();
        let ops = c.b.ops.clone();
        let toffoli = ops.iter()
            .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count();
        let (nq, nb, _, _) = analyze_ops(ops.iter());
        let nq = (nq as usize).max(ids.iter().map(|id| id.0 as usize + 1).max().unwrap());
        let mut is_data = vec![false; nq];
        for id in &ids { is_data[id.0 as usize] = true; }
        let case = Case { ops, ids, is_data, n, m, window, nq, nb: nb as usize, toffoli,
            ancilla: nq - 2 * n - m - 2, carry_room };
        // Review (T model): the emitted Toffoli count must be exactly the
        // cascade (2n) + one capture per leaf (z) + one CCX per visited
        // internal engine node + 3 per visited top quarter (the fold), or 0
        // when the effective range is empty; coherent clears double the
        // engine part. This pins the section-4 deviation to the engine tree.
        let (predicted, _) = case.t_model();
        assert_eq!(case.toffoli, predicted, "T model mismatch [{}]", case.describe());
        case
    }

    /// Effective leaf range [lo, hi] as the primitive computes it (addresses
    /// in the window, inside the address space, with 1..=n cells), or None.
    fn effective(&self) -> Option<(usize, usize)> {
        let hi_addr = self.window.base + (1usize << self.m) - 1;
        let mut eff: Option<(usize, usize)> = None;
        for a in self.window.lo.max(self.window.base)..=self.window.hi.min(hi_addr) {
            let Some(k) = self.window.cells(a) else { continue };
            if k == 0 || k > self.n { continue; }
            eff = Some(match eff { None => (a, a), Some((l, h)) => (l.min(a), h.max(a)) });
        }
        eff
    }

    fn leaves(&self) -> usize {
        self.effective().map_or(0, |(lo, hi)| hi - lo + 1)
    }

    /// (predicted T, design T = 2n + 2z) for this circuit under the current
    /// engine switches.
    fn t_model(&self) -> (usize, usize) {
        let z = self.leaves();
        let Some((lo, hi)) = self.effective() else { return (0, 0) };
        let coherent = std::env::var("MIDQ_ONEHOT_COHERENT").ok().as_deref() == Some("1");
        let nofold = std::env::var("MIDQ_ONEHOT_NOFOLD").ok().as_deref() == Some("1");
        let (nodes, quarters) = engine_model(self.m, lo - self.window.base, hi - self.window.base, nofold);
        let engine = nodes + 3 * quarters;
        let engine = if !nofold && self.m >= 5 {
            let fold = if self.m >= 7 { 4 } else { 3 };
            let size = 1usize << (self.m-fold);
            let lo = lo - self.window.base;
            let hi = hi - self.window.base;
            let groups: Vec<usize> = (0..1usize<<fold).filter(|g| g*size <= hi && (g+1)*size > lo).collect();
            let nodes: usize = groups.iter().map(|g| count_visit(self.m-fold, g*size, lo, hi)).sum();
            if coherent { 2*nodes + (4*fold-2) + (2*fold-3)*(groups.len()-1) }
            else { nodes + (2*fold-1) + (fold-1)*(groups.len()-1) }
        } else { engine * if coherent { 2 } else { 1 } };
        let cascade = if !coherent && std::env::var("MIDQ_CAPTURE_CHUNKS").ok().as_deref() != Some("0") {
            let end = self.window.cells(lo).unwrap().max(self.window.cells(hi).unwrap());
            let (prefix, chunks) = super::carry::plan(end, self.carry_room);
            let replay: usize = chunks.iter().take(chunks.len().saturating_sub(1)).map(|n| n - 1).sum();
            2 * prefix + (end - prefix) + replay
        } else { 2 * self.n };
        let t = cascade + z + engine;
        (t, 2 * self.n + 2 * z)
    }

    fn describe(&self) -> String {
        let (_, design) = self.t_model();
        format!("n={} m={} z={} window=[{},{}] {:?} base={} T={} (design 2n+2z={}) ancilla_wires={}",
            self.n, self.m, self.leaves(), self.window.lo, self.window.hi, self.window.field, self.window.base,
            self.toffoli, design, self.ancilla)
    }

    fn idx_v(&self, i: usize) -> usize { i }
    fn idx_u(&self, i: usize) -> usize { self.n + i }
    fn idx_addr(&self, i: usize) -> usize { 2 * self.n + i }
    fn idx_root(&self) -> usize { 2 * self.n + self.m }
    fn idx_out(&self) -> usize { 2 * self.n + self.m + 1 }

    fn addr_of(&self, cols: &[u64], s: usize) -> usize {
        (0..self.m).map(|i| (((cols[self.idx_addr(i)] >> s) & 1) as usize) << i).sum()
    }

    /// Cells inside the field for shot `s` when it captures (root = 1, address
    /// in the window, k >= 1), else 0.
    fn active_cells(&self, cols: &[u64], s: usize) -> usize {
        if (cols[self.idx_root()] >> s) & 1 == 0 { return 0; }
        let addr = self.addr_of(cols, s) + self.window.base; // true address
        if addr < self.window.lo || addr > self.window.hi { return 0; }
        self.window.cells(addr).unwrap_or(0)
    }

    /// The expected `out` column (bit s = shot s): out ^= [v mod 2^k < u mod 2^k].
    fn expected_out(&self, cols: &[u64]) -> u64 {
        let mut kmask = [0u64; MAX_N]; // kmask[i]: shots whose field contains cell i
        for s in 0..64 {
            let k = self.active_cells(cols, s);
            for slot in kmask.iter_mut().take(k) { *slot |= 1u64 << s; }
        }
        let (mut decided, mut lt) = (0u64, 0u64);
        for i in (0..self.n).rev() {
            let (vi, ui) = (cols[self.idx_v(i)], cols[self.idx_u(i)]);
            let ne = (vi ^ ui) & kmask[i] & !decided;
            lt |= ne & ui;
            decided |= ne;
        }
        cols[self.idx_out()] ^ lt
    }

    /// Apply the circuit (checking every reset), return the data columns.
    fn apply(&self, sim: &mut Simulator<'_, Measurements>, live: u64) -> Vec<u64> {
        crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::predicate_clear_selftest::checked_apply(
            sim, &self.ops, live);
        assert_eq!(sim.phase & live, 0, "phase error [{}]", self.describe());
        let cols: Vec<u64> = self.ids.iter().map(|&id| sim.qubit(id) & live).collect();
        for (q, &value) in sim.qubits.iter().enumerate() {
            if !self.is_data[q] {
                assert_eq!(value & live, 0, "dirty ancilla {q} [{}]", self.describe());
            }
        }
        cols
    }

    /// One batch of up to 64 shots given as data columns: forward check, then
    /// the same circuit again must restore the input (self-inverse).
    fn check_batch(&self, cols: &[u64], live: u64, meas: &mut Measurements, twice: bool) {
        let mut sim = Simulator::new(self.nq, self.nb + 1, meas);
        for (i, &id) in self.ids.iter().enumerate() {
            *sim.qubit_mut(id) = cols[i] & live;
        }
        let got = self.apply(&mut sim, live);
        let mut want: Vec<u64> = cols.iter().map(|c| c & live).collect();
        want[self.idx_out()] = self.expected_out(cols) & live;
        if got != want {
            for s in 0..64 {
                if live >> s & 1 == 0 { continue; }
                let col = |c: &[u64], i: usize| (c[i] >> s) & 1;
                let diff: Vec<usize> = (0..self.ids.len()).filter(|&i| col(&got, i) != col(&want, i)).collect();
                if diff.is_empty() { continue; }
                panic!("mismatch [{}] shot {s} addr={} root={} out_in={} want_out={} got_out={} wrong data cols {:?}",
                    self.describe(), self.addr_of(cols, s), col(cols, self.idx_root()), col(cols, self.idx_out()),
                    col(&want, self.idx_out()), col(&got, self.idx_out()), diff);
            }
        }
        if twice {
            let back = self.apply(&mut sim, live);
            let input: Vec<u64> = cols.iter().map(|c| c & live).collect();
            assert_eq!(back, input, "second application did not restore the input [{}]", self.describe());
        }
    }
}

fn shot_mask(count: usize) -> u64 {
    if count >= 64 { u64::MAX } else { (1u64 << count) - 1 }
}

/// Exhaustive over the packed input word (bit i of the word = data qubit i):
/// `free_bits` enumerated (the enumeration index's bit j drives data bit
/// free_bits[j]), `fixed` bits ORed in. Batches of 64 consecutive indices, so
/// the low six free bits are the fixed shot patterns.
fn exhaustive_words(case: &Case, free_bits: &[usize], fixed: u64, meas: &mut Measurements, twice: bool) -> usize {
    const PATTERN: [u64; 6] = [
        0xAAAA_AAAA_AAAA_AAAA, 0xCCCC_CCCC_CCCC_CCCC, 0xF0F0_F0F0_F0F0_F0F0,
        0xFF00_FF00_FF00_FF00, 0xFFFF_0000_FFFF_0000, 0xFFFF_FFFF_0000_0000,
    ];
    let total = 1usize << free_bits.len();
    let mut cols = vec![0u64; case.ids.len()];
    for (i, col) in cols.iter_mut().enumerate() {
        *col = if (fixed >> i) & 1 == 1 { u64::MAX } else { 0 };
    }
    let mut checked = 0;
    for first in (0..total).step_by(64) {
        let count = 64.min(total - first);
        for (j, &bit) in free_bits.iter().enumerate() {
            cols[bit] = if j < 6 { PATTERN[j] } else if (first >> j) & 1 == 1 { u64::MAX } else { 0 };
        }
        case.check_batch(&cols, shot_mask(count), meas, twice);
        checked += count;
    }
    checked
}

struct Rng(sha3::Shake256Reader);
impl Rng {
    fn new(label: &str) -> Self {
        let mut hash = Shake256::default();
        hash.update(b"packed-capture-compare-operands-v1");
        hash.update(label.as_bytes());
        Rng(hash.finalize_xof())
    }
    fn u64(&mut self) -> u64 {
        let mut buf = [0u8; 8];
        self.0.read(&mut buf);
        u64::from_le_bytes(buf)
    }
    fn below(&mut self, n: usize) -> usize { (self.u64() % n as u64) as usize }
}

/// Random batches: v, u uniformly random on all n cells (FOREIGN bits above the
/// capture position), address mostly inside the window (some shots just
/// outside it), root 1 on 7/8 of the shots, out random; a quarter of the shots
/// tie from a random cell upward (equal operands included). With `tie` the
/// bits above the field are copied from v to u on every shot, so the witness
/// must also equal the full compare [v < u] (asserted per shot).
fn random_batches(case: &Case, batches: usize, tie: bool, meas: &mut Measurements, rng: &mut Rng) -> usize {
    let n = case.n;
    let mut checked = 0;
    for _ in 0..batches {
        let mut cols = vec![0u64; case.ids.len()];
        for i in 0..n {
            cols[case.idx_v(i)] = rng.u64();
            cols[case.idx_u(i)] = rng.u64();
        }
        let mut tmask = [0u64; MAX_N]; // tmask[i]: shots whose u[i] is copied from v[i]
        for s in 0..64 {
            let base = case.window.base;
            let lo = case.window.lo.saturating_sub(2).max(base);
            let hi = (case.window.hi + 2).min(base + (1 << case.m) - 1);
            let addr = lo + rng.below(hi - lo + 1); // true address; the register holds addr - base
            for i in 0..case.m {
                cols[case.idx_addr(i)] |= ((((addr - base) >> i) & 1) as u64) << s;
            }
            cols[case.idx_root()] |= ((rng.below(8) != 0) as u64) << s;
            cols[case.idx_out()] |= (rng.below(2) as u64) << s;
            let mut from = n;
            if tie {
                from = case.window.cells(addr).unwrap_or(n).min(n);
            }
            if rng.below(4) == 0 {
                from = from.min(rng.below(n + 1));
            }
            for slot in tmask.iter_mut().take(n).skip(from) { *slot |= 1u64 << s; }
        }
        for i in 0..n {
            let (vi, ui) = (cols[case.idx_v(i)], cols[case.idx_u(i)]);
            cols[case.idx_u(i)] = (ui & !tmask[i]) | (vi & tmask[i]);
        }
        if tie {
            for s in 0..64 {
                let k = case.active_cells(&cols, s);
                if k == 0 { continue; }
                let bit = |i: usize| (cols[i] >> s) & 1;
                let cmp = |cells: usize| (0..cells).rev()
                    .find(|&i| bit(case.idx_v(i)) != bit(case.idx_u(i)))
                    .map_or(0, |i| bit(case.idx_u(i)));
                assert_eq!(cmp(n), cmp(k), "tie construction");
            }
        }
        case.check_batch(&cols, u64::MAX, meas, true);
        checked += 64;
    }
    checked
}

fn env_set(name: &str, on: bool) {
    if on { std::env::set_var(name, "1"); } else { std::env::remove_var(name); }
}

// ---------------------------------------------------------------------------
// Review additions (adversarial cases): the engine T model, a per-shot batch
// builder, synthetic edge patterns at the maximum width, and real states
// from the classical model laid out on the rings for every consumer shape.
// ---------------------------------------------------------------------------

/// Internal engine nodes (1 CCX each) that `visit` emits for the address
/// subtree `[prefix, prefix + 2^bits)` pruned to `[lo, hi]`.
fn count_visit(bits: usize, prefix: usize, lo: usize, hi: usize) -> usize {
    let span = 1usize << bits;
    if prefix + span <= lo || prefix > hi || bits == 0 {
        return 0;
    }
    let half = 1usize << (bits - 1);
    1 + count_visit(bits - 1, prefix, lo, hi) + count_visit(bits - 1, prefix + half, lo, hi)
}

/// (internal nodes, visited top quarters) of the engine for an `m`-bit
/// address over the leaf range `[lo, hi]` (the fold applies for m >= 3).
fn engine_model(m: usize, lo: usize, hi: usize, nofold: bool) -> (usize, usize) {
    if m < 3 || nofold {
        return (count_visit(m, 0, lo, hi), 0);
    }
    let quarter = 1usize << (m - 2);
    let quarters: Vec<usize> = (0..4).filter(|q| q * quarter <= hi && (q + 1) * quarter > lo).collect();
    (quarters.iter().map(|&q| count_visit(m - 2, q * quarter, lo, hi)).sum(), quarters.len())
}

/// A batch of up to 64 shots filled one shot at a time from cell vectors.
struct Batch {
    cols: Vec<u64>,
    live: u64,
    next: usize,
}

impl Batch {
    fn new(case: &Case) -> Batch {
        Batch { cols: vec![0u64; case.ids.len()], live: 0, next: 0 }
    }

    fn full(&self) -> bool { self.next == 64 }

    /// Add one shot: `v`/`u` are the cascade cells (cell 0 first, exactly
    /// `case.n` of them), `addr` the address value, `root`/`out` the flags.
    fn shot(&mut self, case: &Case, v: &[bool], u: &[bool], addr: usize, root: bool, out: bool) {
        assert!(self.next < 64 && v.len() == case.n && u.len() == case.n && addr < (1 << case.m));
        let s = self.next;
        for i in 0..case.n {
            if v[i] { self.cols[case.idx_v(i)] |= 1u64 << s; }
            if u[i] { self.cols[case.idx_u(i)] |= 1u64 << s; }
        }
        for i in 0..case.m {
            if (addr >> i) & 1 == 1 { self.cols[case.idx_addr(i)] |= 1u64 << s; }
        }
        if root { self.cols[case.idx_root()] |= 1u64 << s; }
        if out { self.cols[case.idx_out()] |= 1u64 << s; }
        self.live |= 1u64 << s;
        self.next += 1;
    }

    /// Run the batch (forward + second application) and reset it. Returns
    /// the number of shots checked.
    fn flush(&mut self, case: &Case, meas: &mut Measurements) -> usize {
        if self.next == 0 { return 0; }
        case.check_batch(&self.cols, self.live, meas, true);
        let count = self.next;
        for col in self.cols.iter_mut() { *col = 0; }
        self.live = 0;
        self.next = 0;
        count
    }

    /// The witness the harness expects for the shot just added (its truth
    /// from the columns), used to assert that a synthetic pattern really
    /// encodes the intended verdict.
    fn last_expected(&self, case: &Case) -> bool {
        let s = self.next - 1;
        let want = case.expected_out(&self.cols) ^ self.cols[case.idx_out()];
        (want >> s) & 1 == 1
    }
}

/// Synthetic edge patterns on 257-wide cascades with the widest legal windows
/// (z = 257 leaves each): every k in 1..=257, both `FieldEnd` forms, all four
/// measurement modes, applied twice. Verdicts are asserted against the
/// pattern's construction as well as against the circuit.
fn synthetic_cases(checked: &mut usize, report: &mut Vec<String>, modes: &[usize]) {
    const N: usize = 257;
    let asc = Case::build(N, 9, CaptureWindow { lo: 1, hi: 257, field: FieldEnd::AddrMinus(0), base: 0 });
    let desc = Case::build(N, 9, CaptureWindow { lo: 0, hi: 256, field: FieldEnd::BaseMinusAddr(257), base: 0 });
    let clamp = Case::build(N, 9, CaptureWindow { lo: 301, hi: 1000, field: FieldEnd::AddrMinus(300), base: 0 });
    report.push(format!("{} [synthetic: widest ascending window]", asc.describe()));
    report.push(format!("{} [synthetic: widest descending window]", desc.describe()));
    report.push(format!("{} [synthetic: hi clamped to the 9-bit address space]", clamp.describe()));
    let mut rng = Rng::new("synthetic");
    // Pattern kinds: (v, u, intended witness) for a field of k cells.
    #[derive(Clone, Copy, Debug)]
    enum Kind {
        AllZero, AllOnes, VZeroUOnes, VOnesUZero,
        TieAdjacent(bool, bool), LessAdjacent10, GreaterAdjacent01,
        UTopOfField, UJustAbove, VTopUAllOnes, VPow2UPow2Minus1, VPow2Minus1UPow2,
        RandomTie, RandomAboveOnly,
    }
    let kinds = [
        Kind::AllZero, Kind::AllOnes, Kind::VZeroUOnes, Kind::VOnesUZero,
        Kind::TieAdjacent(false, false), Kind::TieAdjacent(false, true),
        Kind::TieAdjacent(true, false), Kind::TieAdjacent(true, true),
        Kind::LessAdjacent10, Kind::GreaterAdjacent01,
        Kind::UTopOfField, Kind::UJustAbove, Kind::VTopUAllOnes,
        Kind::VPow2UPow2Minus1, Kind::VPow2Minus1UPow2, Kind::RandomTie, Kind::RandomAboveOnly,
    ];
    let pattern = |kind: Kind, k: usize, rng: &mut Rng| -> (Vec<bool>, Vec<bool>, bool) {
        let mut v = vec![false; N];
        let mut u = vec![false; N];
        let rand_above = |v: &mut Vec<bool>, u: &mut Vec<bool>, from: usize, rng: &mut Rng| {
            for i in from..N { v[i] = rng.below(2) == 1; u[i] = rng.below(2) == 1; }
        };
        let want = match kind {
            Kind::AllZero => false,
            Kind::AllOnes => { v.iter_mut().for_each(|b| *b = true); u.iter_mut().for_each(|b| *b = true); false }
            Kind::VZeroUOnes => { u.iter_mut().for_each(|b| *b = true); true }
            Kind::VOnesUZero => { v.iter_mut().for_each(|b| *b = true); false }
            Kind::TieAdjacent(vk, uk) => {
                for i in 0..k { let b = rng.below(2) == 1; v[i] = b; u[i] = b; }
                rand_above(&mut v, &mut u, k + 1, rng);
                if k < N { v[k] = vk; u[k] = uk; }
                false
            }
            Kind::LessAdjacent10 => {
                // v_lo < u_lo decided at a random cell, (v[k], u[k]) = (1, 0)
                // would flip a full compare to "greater": the witness stays 1.
                let d = rng.below(k);
                for i in 0..k { let b = rng.below(2) == 1; v[i] = b; u[i] = b; }
                v[d] = false; u[d] = true;
                rand_above(&mut v, &mut u, k + 1, rng);
                if k < N { v[k] = true; u[k] = false; }
                true
            }
            Kind::GreaterAdjacent01 => {
                let d = rng.below(k);
                for i in 0..k { let b = rng.below(2) == 1; v[i] = b; u[i] = b; }
                v[d] = true; u[d] = false;
                rand_above(&mut v, &mut u, k + 1, rng);
                if k < N { v[k] = false; u[k] = true; }
                false
            }
            Kind::UTopOfField => { u[k - 1] = true; true }
            Kind::UJustAbove => { if k < N { u[k] = true; } false }
            Kind::VTopUAllOnes => { v[k - 1] = true; for i in 0..k { u[i] = true; } k >= 2 }
            Kind::VPow2UPow2Minus1 => { v[k - 1] = true; for i in 0..k - 1 { u[i] = true; } false }
            Kind::VPow2Minus1UPow2 => { for i in 0..k - 1 { v[i] = true; } u[k - 1] = true; true }
            Kind::RandomTie => {
                for i in 0..k { let b = rng.below(2) == 1; v[i] = b; u[i] = b; }
                rand_above(&mut v, &mut u, k, rng);
                false
            }
            Kind::RandomAboveOnly => {
                // field all zero, arbitrary bits above (incl. adjacent): 0.
                rand_above(&mut v, &mut u, k, rng);
                false
            }
        };
        (v, u, want)
    };
    for &mode in modes {
        let mut meas = Measurements::new(mode, "synthetic");
        for kind in kinds {
            for (case, out_in, root) in [(&asc, false, true), (&asc, true, true), (&desc, false, true), (&asc, false, false)] {
                let mut batch = Batch::new(case);
                for k in 1..=N {
                    let (v, u, want) = pattern(kind, k, &mut rng);
                    let addr = match case.window.field {
                        FieldEnd::AddrMinus(off) => k + off,
                        FieldEnd::BaseMinusAddr(base) => base - k,
                    };
                    batch.shot(case, &v, &u, addr, root, out_in);
                    assert_eq!(batch.last_expected(case), want && root, "pattern {kind:?} k={k}");
                    if batch.full() { *checked += batch.flush(case, &mut meas); }
                }
                *checked += batch.flush(case, &mut meas);
            }
        }
        // Off-window addresses with root = 1 on the strongest pattern
        // (v = 0, u = all ones): 0 (k = 0), 258..=511 (above hi, every top
        // quarter incl. the visited one), and the clamped window's shots.
        let mut batch = Batch::new(&asc);
        let (v, u, _) = pattern(Kind::VZeroUOnes, 1, &mut rng);
        for addr in [0usize, 258, 259, 300, 383, 384, 400, 511, 256 + 64, 257].iter().copied() {
            batch.shot(&asc, &v, &u, addr, true, false);
            assert_eq!(batch.last_expected(&asc), addr == 257, "off-window addr {addr}");
        }
        *checked += batch.flush(&asc, &mut meas);
        let mut batch = Batch::new(&clamp);
        for addr in [0usize, 299, 300, 301, 302, 400, 510, 511].iter().copied() {
            let (v, u, _) = pattern(Kind::VZeroUOnes, 1, &mut rng);
            batch.shot(&clamp, &v, &u, addr, true, false);
            assert_eq!(batch.last_expected(&clamp), addr > 300, "clamped window addr {addr}");
        }
        for _ in 0..56 {
            let k = 1 + rng.below(211);
            let (v, u, want) = pattern(kinds[rng.below(kinds.len())], k, &mut rng);
            batch.shot(&clamp, &v, &u, 300 + k, true, rng.below(2) == 1);
            assert_eq!(batch.last_expected(&clamp), want);
        }
        *checked += batch.flush(&clamp, &mut meas);
        // Maximum amounts on the descending form: addr 0 -> k = 257 (the
        // whole cascade), addr 256 -> k = 1, addr 257..=511 -> nothing.
        let mut batch = Batch::new(&desc);
        for addr in [0usize, 1, 255, 256, 257, 258, 383, 384, 511].iter().copied() {
            let (v, u, _) = pattern(Kind::VZeroUOnes, 1, &mut rng);
            batch.shot(&desc, &v, &u, addr, true, false);
            assert_eq!(batch.last_expected(&desc), addr <= 256, "descending addr {addr}");
        }
        for _ in 0..55 {
            let (v, u, _) = pattern(Kind::VPow2Minus1UPow2, 257, &mut rng);
            batch.shot(&desc, &v, &u, 0, true, rng.below(2) == 1);
            assert!(batch.last_expected(&desc));
        }
        *checked += batch.flush(&desc, &mut meas);
    }
}

// --- real states: tools/packed_prefix_model.py::pz_prefix ported ------------

use ruint::aliases::U256;

const NSTEPS: usize = 530;
const RING: usize = 257;

fn p_mod() -> U256 {
    // p = 2^256 - 2^32 - 977 = MAX - (2^32 + 976)
    U256::MAX - U256::from_limbs([(1u64 << 32) + 976, 0, 0, 0])
}

#[derive(Clone, Default)]
struct Pz { a: U256, b: U256, ca: U256, cb: U256, q: u64 }

#[derive(Clone, Copy)]
struct Mul { s2: usize, carry: usize }

#[derive(Clone, Copy)]
struct Div { s_raw: usize, off: usize, s: usize, a_old: U256 }

struct StepRow { pre: Pz, end: Pz, frozen: bool, mul: Option<Mul>, div: Option<Div> }

/// One step of the model on one input; the state is left AFTER the swap.
fn pz_step(st: &mut Pz) -> StepRow {
    let one = U256::from_limbs([1, 0, 0, 0]);
    let pre = st.clone();
    if st.a.is_zero() && st.b == one && st.q == 0 {
        return StepRow { pre: pre.clone(), end: pre, frozen: true, mul: None, div: None };
    }
    let mut mul = None;
    if st.a < st.b && st.q != 0 {
        let s2 = st.q.trailing_zeros() as usize;
        st.q ^= 1u64 << s2;
        assert!(st.cb.bit_len() + s2 <= 256, "cb << s2 overflows");
        let ca_new = st.ca + (st.cb << s2);
        assert!(ca_new >= st.ca, "ca_new overflows");
        let carry = ca_new.bit_len() - st.cb.bit_len() - s2;
        assert!(carry <= 1, "carry not in {{0,1}}");
        st.ca = ca_new;
        mul = Some(Mul { s2, carry });
    }
    let mut div = None;
    if st.ca < st.cb {
        assert!(mul.is_none(), "multiply and division in one step");
        let (ea, eb) = (st.a.bit_len(), st.b.bit_len());
        if ea >= eb {
            let s_raw = ea - eb;
            let off = (st.a < (st.b << s_raw)) as usize;
            if s_raw >= off {
                let s = s_raw - off;
                let bsh = st.b << s;
                assert!(st.a >= bsh);
                let a_old = st.a;
                st.a = st.a - bsh;
                st.q ^= 1u64 << s;
                div = Some(Div { s_raw, off, s, a_old });
            }
        }
    }
    let end = st.clone();
    if st.q == 0 && !st.a.is_zero() {
        std::mem::swap(&mut st.a, &mut st.b);
        std::mem::swap(&mut st.ca, &mut st.cb);
    }
    StepRow { pre, end, frozen: false, mul, div }
}

/// `[val | gap | coef]` on 257 wires: val bit j at wire j, coef bit j at wire
/// 256 - j (asserts the packing invariant).
fn ring_wires(val: &U256, coef: &U256) -> Vec<bool> {
    let mut w = vec![false; RING];
    for j in 0..val.bit_len() { w[j] = val.bit(j); }
    for j in 0..coef.bit_len() {
        assert!(!w[256 - j], "packing invariant bl(val) + bl(coef) <= 257");
        w[256 - j] = coef.bit(j);
    }
    w
}

/// Cells in coefficient bit order: cell i = wire 256 - i.
fn bit_order(w: &[bool]) -> Vec<bool> {
    (0..RING).map(|i| w[256 - i]).collect()
}

/// Rotate the sub-ring `[0, ring)` DOWN by `s` (wire w + s -> w, the low s
/// wires wrap to the top): the value frame after D3 (+D5).
fn rotate_down(w: &mut [bool], ring: usize, s: usize) {
    let old: Vec<bool> = w[..ring].to_vec();
    for i in 0..ring { w[i] = old[(i + s) % ring]; }
}

/// Real states: 64 random inputs per seed are the 64 shots of one batch per
/// step; every consumer shape of the design is laid out classically on the
/// rings and compared against the model's own predicate. Exact forms use the
/// full ring (lo = 0); thin forms use the design's 78-wide window from the
/// batch envelope (the truncated compare is the contract; residue and width
/// misses are counted, not failed).
fn real_state_cases(checked: &mut usize, report: &mut Vec<String>, seeds: u64) {
    let p = p_mod();
    let half = p >> 1usize;
    let one = U256::from_limbs([1, 0, 0, 0]);
    // Exact forms on the full ring.
    let asc = Case::build(RING, 9, CaptureWindow { lo: 1, hi: 257, field: FieldEnd::AddrMinus(0), base: 0 });
    let desc = Case::build(RING, 9, CaptureWindow { lo: 0, hi: 256, field: FieldEnd::BaseMinusAddr(257), base: 0 });
    let mut meas = Measurements::new(3, "real-states");
    let mut meas_forced = Measurements::new(1, "real-states-forced");
    // Coverage counters for the refuters' classes.
    let (mut n_div, mut n_mul, mut n_role, mut n_clear, mut n_frozen) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut gap0, mut ea_eq_wa, mut foreign_at_end_d4, mut foreign_at_end_d9) = (0usize, 0usize, 0usize, 0usize);
    let (mut first_mul, mut first_mul_wide_b, mut b_in_ring, mut foreign_at_end_m10, mut carry1) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut draining, mut off1, mut d_max, mut residue_d4, mut residue_d9, mut residue_m10) = (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut width_miss, mut thin_cases) = (0usize, 0usize);
    for seed in 0..seeds {
        let mut rng = Rng::new(&format!("pz-inputs-{seed}"));
        let mut states: Vec<Pz> = (0..64).map(|_| {
            let x_orig = loop {
                let x = U256::from_limbs([rng.u64(), rng.u64(), rng.u64(), rng.u64()]);
                if !x.is_zero() && x < p { break x; }
            };
            let x = if x_orig > half { p - x_orig } else { x_orig };
            Pz { a: p, b: x, ca: U256::ZERO, cb: one, q: 0 }
        }).collect();
        for step in 0..NSTEPS {
            let rows: Vec<StepRow> = states.iter_mut().map(pz_step).collect();
            let m = if step % 97 == 0 { &mut meas_forced } else { &mut meas };
            // Envelopes of this batch (the schedule's W_A / W_c stand-ins).
            let w_a_div = rows.iter().filter_map(|r| r.div.map(|d| d.a_old.bit_len())).max().unwrap_or(0);
            let w_c_mul = rows.iter().filter(|r| r.mul.is_some())
                .map(|r| r.end.ca.bit_len().max(r.end.cb.bit_len())).max().unwrap_or(0);
            let w_c_pre = rows.iter().filter(|r| !r.frozen)
                .map(|r| r.pre.ca.bit_len().max(r.pre.cb.bit_len())).max().unwrap_or(0);
            let w_a_end = rows.iter().filter(|r| !r.frozen)
                .map(|r| r.end.a.bit_len().max(r.end.b.bit_len())).max().unwrap_or(0);
            // (a) role compute at the step start: role ^= [A < B], capture at
            //     k = 257 - max(e_ca, e_cb); frozen rows have root = 0.
            let mut role = Batch::new(&desc);
            for (i, r) in rows.iter().enumerate() {
                let (e_a, e_b) = (r.pre.a.bit_len(), r.pre.b.bit_len());
                let mm = r.pre.ca.bit_len().max(r.pre.cb.bit_len());
                assert!(e_a.max(e_b) <= 257 - mm, "role precondition at step {step} input {i}");
                let v = ring_wires(&r.pre.a, &r.pre.cb);
                let u = ring_wires(&r.pre.b, &r.pre.ca);
                role.shot(&desc, &v, &u, mm, !r.frozen, i % 3 == 0);
                assert_eq!(role.last_expected(&desc), !r.frozen && r.pre.a < r.pre.b, "role compute step {step}");
                if r.frozen { n_frozen += 1; } else { n_role += 1; }
                if r.pre.a.is_zero() && !r.frozen { draining += 1; }
            }
            *checked += role.flush(&desc, m);
            // (e) role clear at the step end (before the swap): [ca < cb] on
            //     the coefficient cascade, capture at k = 257 - max(e_A, e_B).
            let mut clear = Batch::new(&desc);
            for (i, r) in rows.iter().enumerate() {
                let mm = r.end.a.bit_len().max(r.end.b.bit_len());
                let (e_ca, e_cb) = (r.end.ca.bit_len(), r.end.cb.bit_len());
                assert!(e_ca.max(e_cb) <= 257 - mm, "role clear precondition at step {step} input {i}");
                let v = bit_order(&ring_wires(&r.end.b, &r.end.ca));
                let u = bit_order(&ring_wires(&r.end.a, &r.end.cb));
                clear.shot(&desc, &v, &u, mm, !r.frozen, i % 5 == 0);
                let want = !r.frozen && r.end.ca < r.end.cb;
                assert_eq!(clear.last_expected(&desc), want, "role clear step {step}");
                if r.div.is_some() { assert!(want, "division row must clear role with 1"); }
                if r.mul.is_some() { assert!(!want, "multiply row must clear role with 0"); }
                if !r.frozen { n_clear += 1; }
            }
            *checked += clear.flush(&desc, m);
            // (b) D4: off ^= [(A >> s_raw) < B] in the s_raw frame, capture at
            //     e_B; rows without a division are inactive (root = 0).
            // (c) D9: off ^= [~B < R], R = A_new >> s in the s-frame after the
            //     subtract; the witness is off_old.
            let mut d4 = Batch::new(&asc);
            let mut d9 = Batch::new(&asc);
            for (i, r) in rows.iter().enumerate() {
                let Some(d) = r.div else {
                    // Inactive row: real data, root = 0, out must not move.
                    let v = ring_wires(&r.pre.a, &r.pre.cb);
                    let u = ring_wires(&r.pre.b, &r.pre.ca);
                    let e_b = r.pre.b.bit_len().max(1);
                    d4.shot(&asc, &v, &u, e_b, false, i % 2 == 0);
                    d9.shot(&asc, &v, &u, e_b, false, i % 2 == 1);
                    continue;
                };
                n_div += 1;
                let (e_a, e_b, e_cb) = (d.a_old.bit_len(), r.end.b.bit_len(), r.end.cb.bit_len());
                assert_eq!(e_a, e_b + d.s_raw);
                if e_a + e_cb == 257 { gap0 += 1; }
                if d.off == 1 { off1 += 1; }
                let dd = e_a - r.end.a.bit_len();
                d_max = d_max.max(dd);
                // Ring: the input's own tight ring (e_A = W_A) on odd inputs,
                // the batch envelope on even ones.
                let ring = if i % 2 == 1 { e_a } else { w_a_div };
                if ring == e_a { ea_eq_wa += 1; }
                let mut v = ring_wires(&d.a_old, &r.end.cb);
                rotate_down(&mut v, ring, d.s_raw);
                let u = ring_wires(&r.end.b, &r.end.ca);
                if v[e_b] || u[e_b] { foreign_at_end_d4 += 1; }
                d4.shot(&asc, &v, &u, e_b, true, i % 2 == 0);
                assert_eq!(d4.last_expected(&asc), (d.a_old >> d.s_raw) < r.end.b, "D4 step {step}");
                assert_eq!(d4.last_expected(&asc), d.off == 1, "D4 witness is off");
                // D9: rotate down by s, overwrite the field [0, E) with A_new >> s.
                let e = e_b + d.off;
                let mut r1 = ring_wires(&d.a_old, &r.end.cb);
                rotate_down(&mut r1, ring, d.s);
                let rr = r.end.a >> d.s;
                assert!(rr.bit_len() <= e);
                for j in 0..e { r1[j] = rr.bit(j); }
                let nb: Vec<bool> = ring_wires(&r.end.b, &r.end.ca).iter().map(|b| !b).collect();
                if nb[e_b] || r1[e_b] { foreign_at_end_d9 += 1; }
                d9.shot(&asc, &nb, &r1, e_b, true, i % 2 == 1);
                assert_eq!(d9.last_expected(&asc), d.off == 1, "D9 witness is off_old, step {step}");
            }
            *checked += d4.flush(&asc, m);
            *checked += d9.flush(&asc, m);
            // (d) M10: carry ^= [(ca_new >> D) < cb], D = s2 + carry, on the
            //     coefficient ring rotated by D, capture at e_cb.
            let mut m10 = Batch::new(&asc);
            for (i, r) in rows.iter().enumerate() {
                let Some(mu) = r.mul else {
                    let v = bit_order(&ring_wires(&r.pre.b, &r.pre.ca));
                    let u = bit_order(&ring_wires(&r.pre.a, &r.pre.cb));
                    m10.shot(&asc, &v, &u, r.pre.cb.bit_len().max(1), false, i % 2 == 0);
                    continue;
                };
                n_mul += 1;
                let (e_b, e_ca_new, e_cb) = (r.end.b.bit_len(), r.end.ca.bit_len(), r.end.cb.bit_len());
                if r.pre.ca.is_zero() { first_mul += 1; if e_b >= 226 { first_mul_wide_b += 1; } }
                if mu.carry == 1 { carry1 += 1; }
                let dd = mu.s2 + mu.carry;
                assert_eq!(e_ca_new, e_cb + dd);
                let w_c = if i % 2 == 1 { e_ca_new.max(e_cb) } else { w_c_mul };
                assert!(w_c >= e_ca_new && w_c >= e_cb);
                if e_b + w_c > 256 { b_in_ring += 1; }
                let mut v = bit_order(&ring_wires(&r.end.b, &r.end.ca));
                rotate_down(&mut v, w_c + 1, dd);
                let u = bit_order(&ring_wires(&r.end.a, &r.end.cb));
                if v[e_cb] || u[e_cb] { foreign_at_end_m10 += 1; }
                m10.shot(&asc, &v, &u, e_cb, true, i % 2 == 1);
                assert_eq!(m10.last_expected(&asc), (r.end.ca >> dd) < r.end.cb, "M10 step {step}");
                assert_eq!(m10.last_expected(&asc), mu.carry == 1, "M10 witness is carry, step {step}");
            }
            *checked += m10.flush(&asc, m);
            // Thin forms (design windows from the batch envelope): D4 and D9
            // over [lo_A, W_A) with addresses (lo_A, W_A]; M10 over bits
            // [lo_c, W_c + 1) with addresses (lo_c, W_c]; role compute over
            // [0, 257 - lo_c) with addresses [lo_c, W_c]; role clear over
            // [0, 257 - lo_A') with addresses [lo_A', W_A'].
            if w_a_div > 0 {
                let lo_a = w_a_div.saturating_sub(78);
                let n = w_a_div - lo_a;
                let case = Case::build(n, 9, CaptureWindow { lo: lo_a + 1, hi: w_a_div, field: FieldEnd::AddrMinus(lo_a), base: 0 });
                thin_cases += 1;
                let mut d4 = Batch::new(&case);
                let mut d9 = Batch::new(&case);
                for (i, r) in rows.iter().enumerate() {
                    let Some(d) = r.div else { continue };
                    let e_b = r.end.b.bit_len();
                    if e_b <= lo_a { width_miss += 1; }
                    let mut v = ring_wires(&d.a_old, &r.end.cb);
                    rotate_down(&mut v, w_a_div, d.s_raw);
                    let u = ring_wires(&r.end.b, &r.end.ca);
                    d4.shot(&case, &v[lo_a..w_a_div], &u[lo_a..w_a_div], e_b, true, i % 2 == 0);
                    if e_b > lo_a && d4.last_expected(&case) != (d.off == 1) { residue_d4 += 1; }
                    let e = e_b + d.off;
                    let mut r1 = ring_wires(&d.a_old, &r.end.cb);
                    rotate_down(&mut r1, w_a_div, d.s);
                    let rr = r.end.a >> d.s;
                    for j in 0..e { r1[j] = rr.bit(j); }
                    let nb: Vec<bool> = u.iter().map(|b| !b).collect();
                    d9.shot(&case, &nb[lo_a..w_a_div], &r1[lo_a..w_a_div], e_b, true, i % 2 == 1);
                    if e_b > lo_a && d9.last_expected(&case) != (d.off == 1) { residue_d9 += 1; }
                }
                *checked += d4.flush(&case, m);
                *checked += d9.flush(&case, m);
            }
            if w_c_mul > 0 {
                let lo_c = w_c_mul.saturating_sub(78);
                let n = w_c_mul + 1 - lo_c;
                let case = Case::build(n, 9, CaptureWindow { lo: lo_c + 1, hi: w_c_mul, field: FieldEnd::AddrMinus(lo_c), base: 0 });
                thin_cases += 1;
                let mut m10 = Batch::new(&case);
                for (i, r) in rows.iter().enumerate() {
                    let Some(mu) = r.mul else { continue };
                    let e_cb = r.end.cb.bit_len();
                    if e_cb <= lo_c { width_miss += 1; }
                    let dd = mu.s2 + mu.carry;
                    let mut v = bit_order(&ring_wires(&r.end.b, &r.end.ca));
                    rotate_down(&mut v, w_c_mul + 1, dd);
                    let u = bit_order(&ring_wires(&r.end.a, &r.end.cb));
                    m10.shot(&case, &v[lo_c..w_c_mul + 1], &u[lo_c..w_c_mul + 1], e_cb, true, i % 2 == 1);
                    if e_cb > lo_c && m10.last_expected(&case) != (mu.carry == 1) { residue_m10 += 1; }
                }
                *checked += m10.flush(&case, m);
            }
            if w_c_pre > 0 {
                let lo_c = w_c_pre.saturating_sub(78);
                let case = Case::build(257 - lo_c, 9, CaptureWindow { lo: lo_c, hi: w_c_pre, field: FieldEnd::BaseMinusAddr(257), base: 0 });
                thin_cases += 1;
                let mut role = Batch::new(&case);
                for (i, r) in rows.iter().enumerate() {
                    if r.frozen { continue; }
                    let mm = r.pre.ca.bit_len().max(r.pre.cb.bit_len());
                    let v = ring_wires(&r.pre.a, &r.pre.cb);
                    let u = ring_wires(&r.pre.b, &r.pre.ca);
                    role.shot(&case, &v[..257 - lo_c], &u[..257 - lo_c], mm, true, i % 3 == 1);
                    if mm < lo_c { width_miss += 1; } else {
                        assert_eq!(role.last_expected(&case), r.pre.a < r.pre.b, "thin role compute step {step}");
                    }
                }
                *checked += role.flush(&case, m);
            }
            if w_a_end > 0 {
                let lo_a = w_a_end.saturating_sub(78);
                let case = Case::build(257 - lo_a, 9, CaptureWindow { lo: lo_a, hi: w_a_end, field: FieldEnd::BaseMinusAddr(257), base: 0 });
                thin_cases += 1;
                let mut clear = Batch::new(&case);
                for (i, r) in rows.iter().enumerate() {
                    if r.frozen { continue; }
                    let mm = r.end.a.bit_len().max(r.end.b.bit_len());
                    let v = bit_order(&ring_wires(&r.end.b, &r.end.ca));
                    let u = bit_order(&ring_wires(&r.end.a, &r.end.cb));
                    clear.shot(&case, &v[..257 - lo_a], &u[..257 - lo_a], mm, true, i % 5 == 2);
                    if mm < lo_a { width_miss += 1; } else {
                        assert_eq!(clear.last_expected(&case), r.end.ca < r.end.cb, "thin role clear step {step}");
                    }
                }
                *checked += clear.flush(&case, m);
            }
        }
    }
    // The classes must actually have been exercised.
    assert!(gap0 > 0 && ea_eq_wa > 0 && foreign_at_end_d4 > 0 && foreign_at_end_d9 > 0, "D4/D9 classes not hit");
    assert!(first_mul == 64 * seeds as usize && first_mul_wide_b > 0 && b_in_ring > 0 && foreign_at_end_m10 > 0 && carry1 > 0, "M10 classes not hit");
    assert!(draining > 0 && n_frozen > 0 && off1 > 0 && d_max >= 1, "terminal classes not hit");
    report.push(format!(
        "real states ({} inputs x {NSTEPS} steps, model pz_prefix): role compute {n_role} rows, role clear {n_clear}, \
         D4/D9 {n_div} division rows (R1 gap 0: {gap0}, e_A = W_A: {ea_eq_wa}, foreign bit at wire e_B: D4 {foreign_at_end_d4} / D9 {foreign_at_end_d9}, \
         off = 1: {off1}, max drop d = {d_max}), M10 {n_mul} multiply rows (first multiply ca_old = 0: {first_mul}, of which e_B >= 226: {first_mul_wide_b}; \
         B's bits inside the M3 ring: {b_in_ring}; foreign bit at bit e_cb: {foreign_at_end_m10}; carry = 1: {carry1}), \
         draining rows {draining}, frozen rows {n_frozen}; thin 78-windows: {thin_cases} circuits, width misses {width_miss}, \
         lo residue (truncated compare != model predicate): D4 {residue_d4} / D9 {residue_d9} / M10 {residue_m10}",
        64 * seeds));
}

pub(super) fn run() {
    env_set("MIDQ_ONEHOT_COHERENT", false);
    env_set("MIDQ_ONEHOT_NOFOLD", false);
    phase_clear_tests();
    chunk_pressure_tests();
    borrowed_workspace_tests();
    let mut checked = 0usize;
    let mut report: Vec<String> = Vec::new();

    // 1. Widths 8-12: exhaustive over (v, u) with the capture position sweeping
    //    the whole window [1, n] (k = addr), root = 1, out = 0; applied twice.
    for n in 8..=12usize {
        let m = 4;
        let case = Case::build(n, m, CaptureWindow { lo: 1, hi: n, field: FieldEnd::AddrMinus(0), base: 0 });
        let free: Vec<usize> = (0..2 * n).collect();
        let mut meas = Measurements::new(3, &format!("sweep{n}"));
        for addr in 1..=n {
            let fixed = ((addr as u64) << (2 * n)) | (1u64 << case.idx_root());
            checked += exhaustive_words(&case, &free, fixed, &mut meas, true);
        }
        if n == 12 { report.push(format!("{} [exhaustive sweep]", case.describe())); }
    }

    // 2. Widths 8-9: exhaustive over the FULL input word (v, u, every address
    //    value incl. off-window, root, out) for six window shapes, all four
    //    measurement modes at width 8.
    for n in 8..=9usize {
        let m = 4;
        let windows = [
            CaptureWindow { lo: 1, hi: n, field: FieldEnd::AddrMinus(0), base: 0 },
            CaptureWindow { lo: 0, hi: n, field: FieldEnd::AddrMinus(0), base: 0 },      // addr 0 -> k = 0 dropped
            CaptureWindow { lo: 3, hi: n - 1, field: FieldEnd::AddrMinus(0), base: 0 },  // sub-window
            CaptureWindow { lo: 4, hi: n + 3, field: FieldEnd::AddrMinus(3), base: 0 },  // offset cascade (D4 lo)
            CaptureWindow { lo: 0, hi: n, field: FieldEnd::BaseMinusAddr(n), base: 0 },  // role shape, addr n -> k = 0
            CaptureWindow { lo: 3, hi: n + 1, field: FieldEnd::BaseMinusAddr(n + 2), base: 0 },
        ];
        for (w, window) in windows.iter().enumerate() {
            let case = Case::build(n, m, *window);
            let free: Vec<usize> = (0..2 * n + m + 2).collect();
            let modes: &[usize] = if n == 8 { &[0, 1, 2, 3] } else { &[3] };
            for &mode in modes {
                let mut meas = Measurements::new(mode, &format!("full{n}w{w}"));
                checked += exhaustive_words(&case, &free, 0, &mut meas, true);
            }
        }
    }

    // 3. 78-wide cascades, 9-bit address: D4/D9/M10 shape (k = addr - lo) with
    //    windows inside a top quarter and straddling 128 / 256, and the role
    //    shape (k = base - addr); random operands, foreign bits above k, tie
    //    variant, all four measurement modes.
    let wide = |n: usize, lo: usize, hi: usize, field: FieldEnd, batches: usize,
                checked: &mut usize, report: &mut Vec<String>, label: &str| {
        let case = Case::build(n, 9, CaptureWindow { lo, hi, field, base: 0 });
        let mut rng = Rng::new(&format!("{label}-{n}-{lo}-{hi}"));
        for mode in 0..4 {
            let mut meas = Measurements::new(mode, &format!("{label}-{n}-{lo}-{hi}"));
            *checked += random_batches(&case, batches, false, &mut meas, &mut rng);
            *checked += random_batches(&case, batches, true, &mut meas, &mut rng);
        }
        report.push(format!("{} [{label}]", case.describe()));
    };
    wide(76, 1, 76, FieldEnd::AddrMinus(0), 2, &mut checked, &mut report, "D4 step 378 (design 306)");
    wide(79, 178, 256, FieldEnd::BaseMinusAddr(257), 2, &mut checked, &mut report, "role compute step 378");
    wide(78, 1, 78, FieldEnd::AddrMinus(0), 8, &mut checked, &mut report, "D4 lo_A=0");
    wide(78, 101, 178, FieldEnd::AddrMinus(100), 8, &mut checked, &mut report, "D4 lo_A=100 straddles 128");
    wide(78, 201, 278, FieldEnd::AddrMinus(200), 4, &mut checked, &mut report, "M10 straddles 256");
    wide(78, 179, 256, FieldEnd::BaseMinusAddr(257), 8, &mut checked, &mut report, "role late");
    wide(78, 100, 177, FieldEnd::BaseMinusAddr(178), 4, &mut checked, &mut report, "role mid");

    // 4. 257-wide: the role compare on the full ring (k = 257 - m) at late,
    //    mid and early windows, and the ascending form up to k = 257.
    wide(257, 179, 256, FieldEnd::BaseMinusAddr(257), 6, &mut checked, &mut report, "role 257 late");
    wide(257, 100, 177, FieldEnd::BaseMinusAddr(257), 4, &mut checked, &mut report, "role 257 mid");
    wide(257, 0, 77, FieldEnd::BaseMinusAddr(257), 4, &mut checked, &mut report, "role 257 early");
    wide(257, 180, 257, FieldEnd::AddrMinus(0), 4, &mut checked, &mut report, "D4 257");

    // 4b. Rebased 7-bit addresses (sched.rs EXP_BITS = 7): the register holds
    //     addr - base; the same consumer shapes with the windows expressed in
    //     true units and clipped to the representable range.
    let wide_b = |n: usize, m: usize, lo: usize, hi: usize, field: FieldEnd, base: usize, batches: usize,
                  checked: &mut usize, report: &mut Vec<String>, label: &str| {
        let case = Case::build(n, m, CaptureWindow { lo, hi, field, base });
        let mut rng = Rng::new(&format!("{label}-{n}-{lo}-{hi}-b{base}"));
        for mode in [1usize, 3] {
            let mut meas = Measurements::new(mode, &format!("{label}-{n}-{lo}-{hi}-b{base}"));
            *checked += random_batches(&case, batches, false, &mut meas, &mut rng);
            *checked += random_batches(&case, batches, true, &mut meas, &mut rng);
        }
        report.push(format!("{} [{label}]", case.describe()));
    };
    wide_b(78, 7, 101, 178, FieldEnd::AddrMinus(100), 51, 4, &mut checked, &mut report, "D4 rebased (step ~100: w_a 178, base 51)");
    wide_b(78, 7, 179, 256, FieldEnd::AddrMinus(178), 129, 4, &mut checked, &mut report, "M10 rebased (w_c 256, base 129)");
    wide_b(79, 7, 178, 256, FieldEnd::BaseMinusAddr(257), 129, 4, &mut checked, &mut report, "role compute rebased (w_c 256, base 129)");
    wide_b(257, 7, 100, 177, FieldEnd::BaseMinusAddr(257), 50, 3, &mut checked, &mut report, "role clear rebased (w_a 177, base 50)");
    wide_b(78, 7, 1, 76, FieldEnd::AddrMinus(0), 0, 2, &mut checked, &mut report, "D4 late 7-bit (base 0)");
    wide_b(78, 7, 20, 60, FieldEnd::AddrMinus(0), 40, 2, &mut checked, &mut report, "window clipped below the base");

    // 6. (review) Synthetic edge patterns at the maximum width and the widest
    //    windows; 7. (review) real states from the classical model on the
    //    rings for every consumer shape (role compute/clear, D4, D9, M10).
    synthetic_cases(&mut checked, &mut report, &[0, 1, 2, 3]);
    real_state_cases(&mut checked, &mut report, 3);

    // 5. Engine variants: coherent uncomputes and no top fold.
    for (coherent, nofold) in [(true, false), (false, true), (true, true)] {
        env_set("MIDQ_ONEHOT_COHERENT", coherent);
        env_set("MIDQ_ONEHOT_NOFOLD", nofold);
        let label = format!("coherent={} nofold={}", coherent as u8, nofold as u8);
        let case = Case::build(8, 4, CaptureWindow { lo: 0, hi: 8, field: FieldEnd::AddrMinus(0), base: 0 });
        let free: Vec<usize> = (0..2 * 8 + 4 + 2).collect();
        for mode in [1usize, 3] {
            let mut meas = Measurements::new(mode, &label);
            checked += exhaustive_words(&case, &free, 0, &mut meas, true);
        }
        wide(78, 101, 178, FieldEnd::AddrMinus(100), 3, &mut checked, &mut report, &label);
        // (review) the synthetic and real-state sections under each variant.
        let before = report.len();
        synthetic_cases(&mut checked, &mut report, &[1, 3]);
        real_state_cases(&mut checked, &mut report, 1);
        report.truncate(before);
        report.push(format!("[{label}] synthetic + real-state sections pass"));
    }
    env_set("MIDQ_ONEHOT_COHERENT", false);
    env_set("MIDQ_ONEHOT_NOFOLD", false);

    for line in &report {
        eprintln!("PACKED_CAPTURE_COMPARE T {line}");
    }
    eprintln!("PACKED_CAPTURE_COMPARE PASS: {checked} shots (widths 8-12 exhaustive with the capture \
               position sweeping the window, 78/257-wide random with foreign bits above the capture \
               position, synthetic edge patterns at 257 wide for every k with the widest windows, \
               real pz_prefix states on the rings for role compute/clear, D4, D9 and M10 in the exact \
               and thin-window forms, every circuit's T asserted against the engine model); witness, \
               operands, phase, resets, ancillae and the second application checked");
}

fn chunk_pressure_tests() {
    let saved = std::env::var("MIDQ_CAPTURE_CHUNK_ROOM").ok();
    let mut checked = 0;
    for room in [0usize, 1, 2, 3, 5, 8, 12, 24] {
        std::env::set_var("MIDQ_CAPTURE_CHUNK_ROOM", room.to_string());
        for n in [4usize, 78, 127, 257] {
            let m = (usize::BITS - n.leading_zeros()) as usize;
            for descending in [false, true] {
                let window = CaptureWindow { lo: 0, hi: n, base: 0,
                    field: if descending { FieldEnd::BaseMinusAddr(n) } else { FieldEnd::AddrMinus(0) } };
                let case = Case::build(n, m, window);
                assert!(case.ancilla <= 1 + super::carry::engine_room(m) + room);
                for mode in 0..4 {
                    let label = format!("chunks-n{n}-r{room}-d{descending}-m{mode}");
                    let mut meas = Measurements::new(mode, &label);
                    if n == 4 {
                        checked += exhaustive_words(&case, &(0..2*n+m+2).collect::<Vec<_>>(), 0, &mut meas, true);
                    } else {
                        let mut rng = Rng::new(&label);
                        checked += random_batches(&case, 8, false, &mut meas, &mut rng);
                        checked += random_batches(&case, 8, true, &mut meas, &mut rng);
                    }
                }
            }
        }
        if [0, 3, 12, 24].contains(&room) { phase_clear_tests(); }
    }
    match saved {
        Some(value) => std::env::set_var("MIDQ_CAPTURE_CHUNK_ROOM", value),
        None => std::env::remove_var("MIDQ_CAPTURE_CHUNK_ROOM"),
    }
    eprintln!("PACKED_CAPTURE_CHUNK_PRESSURE PASS {checked} cases, rooms0/1/2/3/5/8/12/24, exact cost/peak, both maps/four measurement modes/all wires/phase/every reset/twice");
}

fn borrowed_workspace_tests() {
    use crate::circuit::BitId;
    use crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::predicate_clear_selftest::checked_apply;
    let saved = std::env::var("MIDQ_CAPTURE_CHUNK_ROOM").ok();
    let mut checked = 0;
    for room in [0usize, 3, 12] {
        std::env::set_var("MIDQ_CAPTURE_CHUNK_ROOM", room.to_string());
        for count_scratch in [1usize, 6, 12, 16] {
            for n in [4usize, 78, 257] {
                let m = (usize::BITS - n.leading_zeros()) as usize;
                for descending in [false, true] {
                    let window = CaptureWindow { lo: 0, hi: n, base: 0,
                        field: if descending { FieldEnd::BaseMinusAddr(n) } else { FieldEnd::AddrMinus(0) } };
                    for erase in [false, true] {
                        for nested in [false, true] {
                            let mut case = Case::build(n, m, window);
                            let mut c = Circuit::new();
                            let v = c.alloc_qreg_bits("test.v", n);
                            let u = c.alloc_qreg_bits("test.u", n);
                            let addr = c.alloc_qreg_bits("test.addr", m);
                            let root = c.alloc_qreg("test.root");
                            let out = c.alloc_qreg("test.out");
                            let scratch = c.alloc_qreg_bits("test.borrowed", count_scratch);
                            let cond = nested.then(|| c.alloc_input_bit());
                            let emit = |c: &mut Circuit| super::capture_with_scratch(c, &root,
                                &v.iter().collect::<Vec<_>>(), &u.iter().collect::<Vec<_>>(),
                                &addr, window, &out, erase, &scratch.iter().collect::<Vec<_>>());
                            if let Some(bit) = cond { c.with_condition(bit, emit); } else { emit(&mut c); }
                            case.ops = c.b.ops.clone();
                            let (nq, nb, _, _) = analyze_ops(case.ops.iter());
                            case.nq = (nq as usize).max(scratch.last().unwrap().id() as usize + 1);
                            assert!(case.nq <= 847);
                            case.nb = nb as usize;
                            case.is_data.resize(case.nq, false);
                            let shots = if n == 4 { 1usize << (2*n+m+2) } else { 1024 };
                            for mode in 0..4 {
                                let mut meas = Measurements::new(mode, "borrowed-capture");
                                for start in (0..shots).step_by(64) {
                                    let mut cols = vec![0u64; case.ids.len()];
                                    for lane in 0..64 {
                                        let index = start+lane;
                                        if n == 4 {
                                            for (bit, col) in cols.iter_mut().enumerate() {
                                                *col |= ((index >> bit & 1) as u64) << lane;
                                            }
                                        } else {
                                            let mut seed = (index as u64+1).wrapping_mul(0x9e3779b97f4a7c15);
                                            for col in cols.iter_mut() {
                                                seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
                                                *col |= (seed & 1) << lane;
                                            }
                                            for bit in 0..m {
                                                cols[case.idx_addr(bit)] &= !(1u64 << lane);
                                                cols[case.idx_addr(bit)] |= ((index >> bit & 1) as u64) << lane;
                                            }
                                        }
                                    }
                                    let predicate = case.expected_out(&cols) ^ cols[case.idx_out()];
                                    if erase { cols[case.idx_out()] = predicate; }
                                    let mut sim = Simulator::new(case.nq, case.nb+1, &mut meas);
                                    for (&id, &value) in case.ids.iter().zip(&cols) { *sim.qubit_mut(id) = value; }
                                    let enabled = if let Some(bit) = cond {
                                        *sim.bit_mut(BitId(bit.raw().into())) = 0xaaaa_aaaa_aaaa_aaaa;
                                        0xaaaa_aaaa_aaaa_aaaa
                                    } else { u64::MAX };
                                    checked_apply(&mut sim, &case.ops, u64::MAX);
                                    assert_eq!(sim.phase, 0, "borrowed phase n={n} room={room} erase={erase}");
                                    let mut expected = cols.clone();
                                    expected[case.idx_out()] ^= predicate & enabled;
                                    assert_eq!(case.ids.iter().map(|&id| sim.qubit(id)).collect::<Vec<_>>(), expected);
                                    for (q, &value) in sim.qubits.iter().enumerate() {
                                        if !case.is_data[q] { assert_eq!(value, 0, "borrowed/allocated wire {q} not restored"); }
                                    }
                                    if !erase {
                                        checked_apply(&mut sim, &case.ops, u64::MAX);
                                        assert_eq!(sim.phase, 0);
                                        assert_eq!(case.ids.iter().map(|&id| sim.qubit(id)).collect::<Vec<_>>(), cols);
                                        for (q, &value) in sim.qubits.iter().enumerate() {
                                            if !case.is_data[q] { assert_eq!(value, 0); }
                                        }
                                    }
                                    checked += 64;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    match saved {
        Some(value) => std::env::set_var("MIDQ_CAPTURE_CHUNK_ROOM", value),
        None => std::env::remove_var("MIDQ_CAPTURE_CHUNK_ROOM"),
    }
    eprintln!("PACKED_CAPTURE_BORROWED PASS {checked} cases, 1/6/12/16clean borrowed bits, rooms0/3/12, XOR/erase/both maps/nested/four measurement modes/all wires/phase/reset");
}

fn phase_clear_tests() {
    use crate::circuit::BitId;
    use crate::point_add::trailmix_port::inversion::shrunken_pz_state_machine::predicate_clear_selftest::checked_apply;
    let mut checked = 0usize;
    let mut nonzero_predicates = 0usize;
    for n in [1usize, 2, 3, 4, 5, 78, 127, 257] {
        let m = (usize::BITS - n.leading_zeros()) as usize;
        for descending in [false, true] {
            for trimmed in [false, true] {
                let base = if trimmed { 37 } else { 0 };
                let window = CaptureWindow {
                    lo: base + if trimmed { n / 3 } else { 0 },
                    hi: base + if trimmed { n - n / 4 } else { n },
                    base,
                    field: if descending { FieldEnd::BaseMinusAddr(base+n) }
                           else { FieldEnd::AddrMinus(base) },
                };
                for nested in [false, true] {
                    let mut case = Case::build(n, m, window);
                    let mut c = Circuit::new();
                    let v = c.alloc_qreg_bits("test.v", n);
                    let u = c.alloc_qreg_bits("test.u", n);
                    let addr = c.alloc_qreg_bits("test.addr", m);
                    let root = c.alloc_qreg("test.root");
                    let out = c.alloc_qreg("test.out");
                    let cond = nested.then(|| c.alloc_input_bit());
                    let emit = |c: &mut Circuit| super::capture_clear(c, &root,
                        &v.iter().collect::<Vec<_>>(), &u.iter().collect::<Vec<_>>(),
                        &addr, window, &out);
                    if let Some(bit) = cond { c.with_condition(bit, emit); }
                    else { emit(&mut c); }
                    case.ops = c.b.ops.clone();
                    let (nq, nb, _, _) = analyze_ops(case.ops.iter());
                    case.nq = (nq as usize).max(case.ids.iter().map(|q| q.0 as usize+1).max().unwrap());
                    case.nb = nb as usize;
                    case.is_data.resize(case.nq, false);
                    let shots = if n <= 5 { 1usize << (2*n + m + 1) } else { 4096 };
                    for mode in 0..4 {
                        let mut meas = Measurements::new(mode, "phase-clear");
                        for start in (0..shots).step_by(64) {
                            let count = 64.min(shots-start);
                            let live = u64::MAX >> (64-count);
                            let mut cols = vec![0u64; case.ids.len()];
                            for lane in 0..count {
                                let index = start+lane;
                                if n <= 5 {
                                    for (bit, col) in cols.iter_mut().enumerate().take(2*n+m+1) {
                                        *col |= ((index >> bit & 1) as u64) << lane;
                                    }
                                } else {
                                    let mut seed = (index as u64+1).wrapping_mul(0x9e3779b97f4a7c15);
                                    for col in cols.iter_mut().take(2*n) {
                                        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
                                        *col |= (seed & 1) << lane;
                                    }
                                    for bit in 0..m { cols[2*n+bit] |= ((index >> bit & 1) as u64) << lane; }
                                    cols[case.idx_root()] |= ((index >> m & 1) as u64) << lane;
                                }
                            }
                            let predicate = case.expected_out(&cols) & live;
                            nonzero_predicates += predicate.count_ones() as usize;
                            cols[case.idx_out()] = predicate;
                            let mut sim = Simulator::new(case.nq, case.nb+1, &mut meas);
                            for (&id, &value) in case.ids.iter().zip(&cols) { *sim.qubit_mut(id) = value; }
                            let enabled = if let Some(bit) = cond {
                                *sim.bit_mut(BitId(bit.raw().into())) = 0xaaaa_aaaa_aaaa_aaaa;
                                0xaaaa_aaaa_aaaa_aaaa
                            } else { u64::MAX };
                            // The legacy Case::apply slices at resets and requires
                            // a stream without PushCondition. Preserve nested masks.
                            checked_apply(&mut sim, &case.ops, live);
                            assert_eq!(sim.phase & live, 0, "phase clear n={n} mode={mode}");
                            for (q, &value) in sim.qubits.iter().enumerate() {
                                if !case.is_data[q] { assert_eq!(value & live, 0, "dirty phase-clear ancilla {q}"); }
                            }
                            let got: Vec<u64> = case.ids.iter().map(|&id| sim.qubit(id) & live).collect();
                            cols[case.idx_out()] &= !enabled;
                            assert_eq!(got, cols, "phase erase n={n} descending={descending} trimmed={trimmed} mode={mode}");
                            checked += count;
                        }
                    }
                }
            }
        }
    }
    assert!(nonzero_predicates > 0);
    eprintln!("PACKED_CAPTURE_PHASE_CLEAR PASS {checked} cases, predicate/precondition, both maps, rebasing, off-window, four measurement modes, nested conditions, all wires/phase/reset");
}
