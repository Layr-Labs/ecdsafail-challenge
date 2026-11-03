//! froghop-double builder: qubit pool, op emission and a small gate IR that can be emitted forward or inverted.
//!
//! Gates are always emitted through `g()`. While a recording is open, they go to the recording instead of the
//! op stream; `play(rec, inverse)` emits a recording forward or as its exact inverse. The only non-self-inverse
//! gates are the measurement-based AND pair: `AndC` (Toffoli into a fresh |0> target, 1 Toffoli) and `AndU`
//! (X-basis measurement of the target plus a classically conditioned CZ fix-up, 0 Toffoli). They invert into
//! each other.

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT, NO_REG};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G {
    X(QubitId),
    Cx(QubitId, QubitId),
    Ccx(QubitId, QubitId, QubitId),
    /// Phase flip where three qubits are all 1 (one Toffoli, self-inverse).
    Ccz(QubitId, QubitId, QubitId),
    Cz(QubitId, QubitId),
    Swap(QubitId, QubitId),
    /// t ^= a & b with t known to be |0> (compute).
    AndC(QubitId, QubitId, QubitId),
    /// t = a & b -> |0> by measurement (uncompute).
    AndU(QubitId, QubitId, QubitId),
    /// X conditioned on a classical bit.
    XIf(QubitId, BitId),
    /// Z conditioned on a classical bit.
    ZIf(QubitId, BitId),
}

pub struct B {
    pub ops: Vec<Op>,
    next_q: u64,
    free_q: BTreeSet<u64>,
    pub live: u64,
    pub peak: u64,
    bit: BitId,
    rec: Vec<Vec<G>>,
    pub tof: u64,
    pub peak_op: usize,
    next_bit: u64,
    /// highest live count since the last `take_sect_peak` (profiling only)
    pub sect_peak: std::cell::Cell<u64>,
}

impl B {
    pub fn new() -> Self {
        let mut b = B { ops: Vec::new(), next_q: 0, free_q: BTreeSet::new(), live: 0, peak: 0, bit: NO_BIT,
                        rec: Vec::new(), tof: 0, next_bit: 10_000, peak_op: 0,
                        sect_peak: std::cell::Cell::new(0) };
        b.bit = BitId(0);
        b
    }

    // ---------------------------------------------------------------- qubits
    #[track_caller]
    pub fn alloc(&mut self) -> QubitId {
        let id = if let Some(&q) = self.free_q.iter().next() {
            self.free_q.remove(&q);
            q
        } else {
            self.next_q += 1;
            self.next_q - 1
        };
        self.live += 1;
        if ZU_OVER.is_some() { let l = std::panic::Location::caller(); let (slot, sect) = super::greedyfrog::l3_profile_context(); zu_own(id, format!("{}:{} {sect} s{slot}", l.file().rsplit('/').next().unwrap_or(""), l.line())); }
        zu_over_cap(self.live, "alloc");
        if self.live > self.sect_peak.get() { self.sect_peak.set(self.live); }
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        QubitId(id)
    }
    #[track_caller]
    pub fn alloc_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.alloc()).collect()
    }
    /// Highest live count since the previous call; restarts the count at the current live (profiling only).
    pub fn take_sect_peak(&self) -> u64 {
        let p = self.sect_peak.get().max(self.live);
        self.sect_peak.set(self.live);
        p
    }
    /// Release a qubit that is |0> on every shot.
    pub fn free(&mut self, q: QubitId) {
        assert!(self.rec.is_empty(), "free inside a recording");
        assert!(self.free_q.insert(q.0), "double free q{}", q.0);
        self.live -= 1;
        zu_disown(q.0);
    }
    pub fn free_n(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    pub fn width(&self) -> u64 {
        self.next_q
    }
    /// Diagnostic position in the current recording, or in the emitted stream.
    pub fn mark_pos(&self) -> usize {
        self.rec.last().map_or(self.ops.len(), Vec::len)
    }
    /// Read-only gate-cost probe for a suffix of the active recording or emitted stream.
    pub fn diagnostic_expected_from(&self, pos: usize) -> f64 {
        if let Some(r) = self.rec.last() {
            r[pos..].iter().filter(|g| matches!(g, G::Ccx(..) | G::Ccz(..) | G::AndC(..))).count() as f64
        } else {
            super::counts(&self.ops[pos..]).2
        }
    }

    // ---------------------------------------------------------------- registers
    pub fn declare_qubits(&mut self, reg: u64, qs: &[QubitId]) {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        for &q in qs {
            self.raw(Op { kind: OperationType::AppendToRegister, q_target: q, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
    }
    pub fn declare_bits(&mut self, reg: u64, n: usize) -> Vec<BitId> {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        let bs: Vec<BitId> = (0..n).map(|i| BitId(1 + reg * 1000 + i as u64)).collect();
        for &b in &bs {
            self.raw(Op { kind: OperationType::AppendToRegister, c_target: b, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
        bs
    }

    // ---------------------------------------------------------------- emission
    fn raw(&mut self, op: Op) {
        debug_assert!({ op.validate(); true });
        let _ = NO_REG;
        self.ops.push(op);
    }
    fn emit(&mut self, g: G, inverse: bool) {
        let e = |kind, t: QubitId, c1: QubitId, c2: QubitId| Op { kind, q_target: t, q_control1: c1, q_control2: c2,
                                                             ..Op::empty() };
        match g {
            G::X(t) => self.raw(e(OperationType::X, t, NO_QUBIT, NO_QUBIT)),
            G::Cx(c, t) => self.raw(e(OperationType::CX, t, c, NO_QUBIT)),
            G::Cz(a, b) => self.raw(e(OperationType::CZ, b, a, NO_QUBIT)),
            G::Swap(a, b) => self.raw(e(OperationType::Swap, b, a, NO_QUBIT)),
            G::Ccx(a, b, t) => {
                self.tof += 1;
                self.raw(e(OperationType::CCX, t, a, b))
            }
            G::Ccz(a, b, c) => {
                self.tof += 1;
                self.raw(e(OperationType::CCZ, c, a, b))
            }
            G::XIf(t, c) => self.raw(Op { kind: OperationType::X, q_target: t, c_condition: c, ..Op::empty() }),
            G::ZIf(t, c) => self.raw(Op { kind: OperationType::Z, q_target: t, c_condition: c, ..Op::empty() }),
            G::AndC(a, b, t) | G::AndU(a, b, t) => {
                let compute = matches!(g, G::AndC(..)) != inverse;
                if compute {
                    self.tof += 1;
                    self.raw(e(OperationType::CCX, t, a, b));
                } else {
                    let m = self.bit;
                    self.raw(Op { kind: OperationType::Hmr, q_target: t, c_target: m, ..Op::empty() });
                    self.raw(Op { kind: OperationType::CZ, q_target: b, q_control1: a, c_condition: m,
                                  ..Op::empty() });
                }
            }
        }
    }
    /// Emit one gate (or record it if a recording is open).
    pub fn g(&mut self, g: G) {
        if let Some(r) = self.rec.last_mut() {
            r.push(g);
        } else {
            self.emit(g, false);
        }
    }
    pub fn begin(&mut self) {
        self.rec.push(Vec::new());
    }
    pub fn end(&mut self) -> Vec<G> {
        self.rec.pop().expect("no recording")
    }
    /// Emit a recording forward or as its inverse (into the enclosing recording if one is open).
    pub fn play(&mut self, r: &[G], inverse: bool) {
        if inverse {
            for &g in r.iter().rev() {
                let gi = match g {
                    G::AndC(a, b, t) => G::AndU(a, b, t),
                    G::AndU(a, b, t) => G::AndC(a, b, t),
                    other => other,
                };
                self.g(gi);
            }
        } else {
            for &g in r {
                self.g(g);
            }
        }
    }

    // ---------------------------------------------------------------- gate helpers
    pub fn x(&mut self, t: QubitId) {
        self.g(G::X(t));
    }
    pub fn cx(&mut self, c: QubitId, t: QubitId) {
        self.g(G::Cx(c, t));
    }
    pub fn ccx(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::Ccx(a, b, t));
    }
    pub fn cz(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Cz(a, b));
    }
    pub fn ccz(&mut self, a: QubitId, b: QubitId, c: QubitId) {
        self.g(G::Ccz(a, b, c));
    }
    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Swap(a, b));
    }
    pub fn and_c(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndC(a, b, t));
    }
    pub fn and_u(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndU(a, b, t));
    }
    pub fn x_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::XIf(t, c));
    }
    pub fn z_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::ZIf(t, c));
    }
    // (the direct CCZ helper of LEVER-AUDIT OR-CCZ now goes through the self-inverse `G::Ccz` variant above, so it
    // can also sit inside a recording; the emitted op is unchanged: CCZ with q_target c, controls a, b, one Toffoli)
    /// A direct phase gate for use inside an emitted classical condition block.
    pub fn z(&mut self, t: QubitId) {
        assert!(self.rec.is_empty(), "Z in recording needs a reversible G variant");
        self.raw(Op { kind: OperationType::Z, q_target: t, ..Op::empty() });
    }
    /// Condition a contiguous emitted block on one measurement receipt.
    pub fn push_condition(&mut self, c: BitId) {
        assert!(self.rec.is_empty(), "condition block inside a recording");
        assert_ne!(c, NO_BIT);
        self.raw(Op { kind: OperationType::PushCondition, c_condition: c, ..Op::empty() });
    }
    /// Invert a classical bit (under the open condition blocks); no qubits, no Toffoli.
    pub fn bit_invert(&mut self, c: BitId) {
        assert!(self.rec.is_empty(), "bit invert inside a recording");
        self.raw(Op { kind: OperationType::BitInvert, c_target: c, ..Op::empty() });
    }
    pub fn pop_condition(&mut self) {
        assert!(self.rec.is_empty(), "condition block inside a recording");
        self.raw(Op { kind: OperationType::PopCondition, ..Op::empty() });
    }
    /// X-basis measurement of q into classical bit c (q -> |0>). Not invertible; never inside a recording.
    pub fn hmr_to(&mut self, q: QubitId, c: BitId) {
        assert!(self.rec.is_empty());
        self.raw(Op { kind: OperationType::Hmr, q_target: q, c_condition: NO_BIT, c_target: c, ..Op::empty() });
    }
    /// Take a specific free qubit back out of the pool.
    #[track_caller]
    pub fn acquire(&mut self, q: QubitId) {
        assert!(self.free_q.remove(&q.0), "acquire of a busy qubit q{}", q.0);
        self.live += 1;
        if ZU_OVER.is_some() { let l = std::panic::Location::caller(); let (slot, sect) = super::greedyfrog::l3_profile_context(); zu_own(q.0, format!("{}:{} acq {sect} s{slot}", l.file().rsplit('/').next().unwrap_or(""), l.line())); }
        zu_over_cap(self.live, "acq");
        if self.live > self.sect_peak.get() { self.sect_peak.set(self.live); }
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
    }
    /// s825 adapter: append an already-remapped foreign op stream and its emitted Toffoli count.
    pub fn push_foreign(&mut self, ops: Vec<Op>, tof: u64) {
        assert!(self.rec.is_empty(), "foreign ops inside a recording");
        for op in ops {
            self.raw(op);
        }
        self.tof += tof;
    }
    pub fn fresh_bits(&mut self, n: usize) -> Vec<BitId> {
        let v: Vec<BitId> = (0..n).map(|i| BitId(self.next_bit + i as u64)).collect();
        self.next_bit += n as u64;
        v
    }
    /// Controlled swap (Fredkin), 1 Toffoli.
    pub fn cswap(&mut self, c: QubitId, a: QubitId, b: QubitId) {
        self.cx(b, a);
        self.ccx(c, a, b);
        self.cx(b, a);
    }
}

#[cfg(test)]
mod r10_c6_condition_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    #[test]
    fn one_r10_c6_condition_block_forced_bits() {
        let mut b = B::new();
        let a = b.alloc();
        let c = b.alloc();
        let t = b.alloc();
        let receipt = b.fresh_bits(1)[0];
        b.push_condition(receipt);
        b.ccx(a, c, t);
        b.z(t);
        b.pop_condition();
        assert_eq!(b.tof, 1);
        for bit in [0, u64::MAX] {
            let mut h = sha3::Shake256::default();
            h.update(b"R10-C6-D1-forced-condition");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, receipt.0 as usize + 1, &mut xof);
            sim.qubits[a.0 as usize] = u64::MAX;
            sim.qubits[c.0 as usize] = u64::MAX;
            sim.bits[receipt.0 as usize] = bit;
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.qubits[t.0 as usize], bit);
            assert_eq!(sim.phase, bit);
            assert_eq!(sim.stats.toffoli_gates, bit.count_ones() as u64);
        }
    }
}

// Fable zuiris dev probe (inert unless P2_OVER=<cap> is set; the official build runs with an empty environment):
// allocation / acquire sites that push live above the cap, keyed by caller line, kind, greedyfrog section and slot.
pub static ZU_OVER: std::sync::LazyLock<Option<u64>> =
    std::sync::LazyLock::new(|| std::env::var("P2_OVER").ok().and_then(|v| v.trim().parse().ok()));
thread_local! {
    static ZU_SITES: std::cell::RefCell<std::collections::BTreeMap<String, (u64, u64)>> = std::cell::RefCell::new(Default::default());
}
thread_local! {
    static ZU_OWNER: std::cell::RefCell<std::collections::BTreeMap<u64, String>> = std::cell::RefCell::new(Default::default());
    static ZU_SNAPPED: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}
pub static ZU_SNAP: std::sync::LazyLock<Option<usize>> =
    std::sync::LazyLock::new(|| std::env::var("ZU_SNAP").ok().and_then(|v| v.trim().parse().ok()));
/// record the owner site of a live qubit (P2_OVER only)
pub fn zu_own(q: u64, site: String) { if ZU_OVER.is_some() { ZU_OWNER.with(|m| { m.borrow_mut().insert(q, site); }); } }
pub fn zu_disown(q: u64) { if ZU_OVER.is_some() { ZU_OWNER.with(|m| { m.borrow_mut().remove(&q); }); } }
#[track_caller]
pub fn zu_over_cap(live: u64, kind: &str) {
    let Some(c) = *ZU_OVER else { return };
    if live <= c { return }
    let loc = std::panic::Location::caller();
    let (slot, sect) = super::greedyfrog::l3_profile_context();
    let k = format!("{}:{} {kind} {sect} s{slot}", loc.file().rsplit('/').next().unwrap_or(""), loc.line());
    ZU_SITES.with(|m| { let mut m = m.borrow_mut(); let e = m.entry(k.clone()).or_insert((0, 0)); e.0 += 1; e.1 = e.1.max(live); });
    // ZU_SNAP=<slot>: at the first over-cap event on that slot, print the owner-site histogram of every live qubit
    if let Some(sl) = *ZU_SNAP { if sl == slot && ZU_SNAPPED.with(|s| s.get()) < 2 {
        ZU_SNAPPED.with(|s| s.set(s.get() + 1));
        let mut h: std::collections::BTreeMap<String, Vec<u64>> = Default::default();
        ZU_OWNER.with(|m| for (q, s) in m.borrow().iter() { h.entry(s.clone()).or_default().push(*q); });
        eprintln!("ZUSNAP at {k} live {live}: {} owned lanes", h.values().map(|v| v.len()).sum::<usize>());
        for (s, qs) in h.iter() { eprintln!("ZUSNAP {:5} {s} q[{}..{}]", qs.len(), qs[0], qs[qs.len() - 1]); }
    } }
}
pub fn zu_over_dump() {
    if ZU_OVER.is_none() { return }
    ZU_SITES.with(|m| for (k, (n, l)) in m.borrow().iter() { eprintln!("OVERLOC {n} live<={l} {k}"); });
}
