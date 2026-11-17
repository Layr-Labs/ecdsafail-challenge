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

fn fable_chk() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("FABLE_CHK").is_some());
    *E
}
fn r8_freechk() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R8_FREECHK").is_some());
    *E
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
    /// R8-ROOM0 dev instrument: open condition blocks (profiling only)
    pub cdepth: i32,
}

impl B {
    pub fn new() -> Self {
        let mut b = B { ops: Vec::new(), next_q: 0, free_q: BTreeSet::new(), live: 0, peak: 0, bit: NO_BIT,
                        rec: Vec::new(), tof: 0, next_bit: 10_000, peak_op: 0,
                        sect_peak: std::cell::Cell::new(0), cdepth: 0 };
        b.bit = BitId(0);
        b
    }

    // ---------------------------------------------------------------- qubits
    #[track_caller]
    pub fn alloc(&mut self) -> QubitId {
        let loc = std::panic::Location::caller();
        let id = if let Some(&q) = self.free_q.iter().next() {
            self.free_q.remove(&q);
            q
        } else {
            self.next_q += 1;
            self.next_q - 1
        };
        self.live += 1;
        fb_span_up(self.live, self.ops.len());
        if self.live > self.sect_peak.get() { self.sect_peak.set(self.live); }
        if self.live as u64 > *PEAK_TRAP { panic!("PEAK_TRAP live {} at op {}", self.live, self.ops.len()); }
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        if let Some(c) = *P2_OVER { if self.live > c { p2_over_note(self.live); OVER_LOC.with(|m| { *m.borrow_mut().entry(format!("{}:{} {} s{}", loc.file(), loc.line(), i5::SECT.with(|c| c.get()), super::greedyfrog::p3_cur_slot())).or_insert(0u64) += 1; }); } }
        i5::on_alloc(id, loc, self.live);
        if *R10TRK { R10LOC.with(|m| { m.borrow_mut().insert(id, format!("{}:{}", loc.file().rsplit('/').next().unwrap_or(""), loc.line())); }); }
        if *r8idle::ON { r8idle::IDLE.with(|m| { m.borrow_mut().insert(id, loc); }); }
        QubitId(id)
    }
    /// Schaffhuuserzopf (R14_LA94B): `alloc` that never returns one of the `avoid` ids (lent lanes taken back by id later)
    #[track_caller]
    pub fn alloc_avoid(&mut self, avoid: &[QubitId]) -> QubitId {
        let held: Vec<u64> = avoid.iter().map(|q| q.0).filter(|q| self.free_q.remove(q)).collect();
        // b793b width guard: where every free id is an avoided one, a fresh id would raise the stream's width above the live peak (the scored
        // qubit count is the width); take the lowest avoided id instead
        if !held.is_empty() && self.free_q.is_empty() {
            let h0 = *held.iter().min().unwrap();
            for &h in &held { if h != h0 { self.free_q.insert(h); } }
            let q = self.alloc_exact(h0);
            return q;
        }
        let q = self.alloc();
        for h in held { self.free_q.insert(h); }
        q
    }
    /// `alloc` of the id `h`, which has been removed from the free pool by the caller
    #[track_caller]
    fn alloc_exact(&mut self, h: u64) -> QubitId {
        self.free_q.insert(h);
        self.acquire(QubitId(h));
        QubitId(h)
    }
    #[track_caller]
    pub fn alloc_n(&mut self, n: usize) -> Vec<QubitId> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n { v.push(self.alloc()); }
        v
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
        fb_span_down(self.live, self.ops.len());
        i5::on_free(q.0);
        if *R10TRK { R10LOC.with(|m| { m.borrow_mut().remove(&q.0); }); }
        if *r8idle::ON { r8idle::IDLE.with(|m| { m.borrow_mut().remove(&q.0); }); r8idle::resolve(q.0); }
    }
    pub fn free_n(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    /// Whether q is currently released (R5-FIT799 rebind of lent lanes; no gates)
    pub fn is_free(&self, q: QubitId) -> bool {
        self.free_q.contains(&q.0)
    }
    pub fn width(&self) -> u64 {
        self.next_q
    }
    /// Diagnostic position in the current recording, or in the emitted stream.
    pub fn mark_pos(&self) -> usize {
        self.rec.last().map_or(self.ops.len(), Vec::len)
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
        // q796jc dev trap (inert unless HMR_TRAP=<n>): backtrace at the n-th R / Hmr op of the stream (0-based)
        if matches!(op.kind, OperationType::R | OperationType::Hmr) {
            if let Some(t) = *HMR_TRAP {
                let n = HMR_CNT.with(|c| { let v = c.get(); c.set(v + 1); v });
                if n == t {
                    eprintln!("HMR_TRAP n {n} foreign-local {} ftcall {} op {} q{} slot {} sect {}\n{}", n - FSTART.with(|f| f.get()),
                              super::ftport::builder::FT_CALLNO.with(|c| c.get()), self.ops.len(), op.q_target.0,
                              super::greedyfrog::p3_cur_slot(), i5::SECT.with(|c| c.get()),
                              std::backtrace::Backtrace::force_capture());
                }
            }
        }
        // fable dev check (FABLE_CHK=1, builds too): operand shape (no NO_QUBIT where a qubit is required) and the
        // R8_FREECHK released-lane check
        if fable_chk() { op.validate(); }
        // R8-LANE799 dev check (gate tests only, R8_FREECHK=1): no gate may touch a released lane
        if (cfg!(test) || fable_chk()) && r8_freechk() {
            for q in [op.q_target, op.q_control1, op.q_control2] {
                assert!(q == NO_QUBIT || !self.free_q.contains(&q.0), "R8_FREECHK: op {:?} on released q{} (op {})", op.kind, q.0, self.ops.len());
                assert!(q == NO_QUBIT || q.0 < super::greedyfrog::R8_POISON, "R8_FREECHK: op {:?} on a released register lane q{} (op {})", op.kind, q.0, self.ops.len());
            }
            let qs = [op.q_target, op.q_control1, op.q_control2];
            for i in 0..3 { for j in i + 1..3 {
                assert!(qs[i] == NO_QUBIT || qs[i] != qs[j], "R8_FREECHK: op {:?} repeats q{} (op {})", op.kind, qs[i].0, self.ops.len());
            } }
        }
        if *r8idle::ON { r8idle::touch(&[op.q_target, op.q_control1, op.q_control2]); }
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
        if *r8idle::ON {
            let v: Vec<QubitId> = match g {
                G::X(a) | G::XIf(a, _) | G::ZIf(a, _) => vec![a],
                G::Cx(a, b) | G::Cz(a, b) | G::Swap(a, b) => vec![a, b],
                G::Ccx(a, b, c) | G::AndC(a, b, c) | G::AndU(a, b, c) => vec![a, b, c],
            };
            r8idle::touch(&v);
        }
        if let Some(r) = self.rec.last_mut() {
            r.push(g);
        } else {
            self.emit(g, false);
        }
    }
    /// R6-ROOM799: a recording is open (gates are not emitted yet)
    pub fn recording(&self) -> bool {
        !self.rec.is_empty()
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
    /// A direct CCZ: phase (-1)^(a b c), one Toffoli-class gate and no ancilla (LEVER-AUDIT OR-CCZ). Emitted only, like
    /// `z` (no reversible G variant).
    pub fn ccz(&mut self, a: QubitId, b: QubitId, c: QubitId) {
        assert!(self.rec.is_empty(), "CCZ in recording needs a reversible G variant");
        self.tof += 1;
        self.raw(Op { kind: OperationType::CCZ, q_target: c, q_control1: a, q_control2: b, ..Op::empty() });
    }
    /// A direct phase gate for use inside an emitted classical condition block.
    pub fn z(&mut self, t: QubitId) {
        assert!(self.rec.is_empty(), "Z in recording needs a reversible G variant");
        self.raw(Op { kind: OperationType::Z, q_target: t, ..Op::empty() });
    }
    /// Condition a contiguous emitted block on one measurement receipt.
    pub fn push_condition(&mut self, c: BitId) {
        assert!(self.rec.is_empty(), "condition block inside a recording");
        assert_ne!(c, NO_BIT);
        self.cdepth += 1;
        self.raw(Op { kind: OperationType::PushCondition, c_condition: c, ..Op::empty() });
    }
    /// Invert a classical bit (under the open condition blocks); no qubits, no Toffoli.
    pub fn bit_invert(&mut self, c: BitId) {
        assert!(self.rec.is_empty(), "bit invert inside a recording");
        self.raw(Op { kind: OperationType::BitInvert, c_target: c, ..Op::empty() });
    }
    pub fn pop_condition(&mut self) {
        assert!(self.rec.is_empty(), "condition block inside a recording");
        self.cdepth -= 1;
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
        let loc = std::panic::Location::caller();
        assert!(self.free_q.remove(&q.0), "acquire of a busy qubit q{}", q.0);
        self.live += 1;
        fb_span_up(self.live, self.ops.len());
        // fable dev probe: acquires that push live above the cap are reported like allocs (OVERLOC ... acq)
        if let Some(c) = *P2_OVER { if self.live > c { OVER_LOC.with(|m| { *m.borrow_mut().entry(format!("{}:{} acq{} s{}", loc.file(), loc.line(), i5::SECT.with(|c| c.get()), super::greedyfrog::p3_cur_slot())).or_insert(0u64) += 1; }); } }
        if *R10TRK { R10LOC.with(|m| { m.borrow_mut().insert(q.0, format!("acq {}:{}", loc.file().rsplit('/').next().unwrap_or(""), loc.line())); }); }
        if self.live > self.sect_peak.get() { self.sect_peak.set(self.live); }
        if self.live as u64 > *PEAK_TRAP { panic!("PEAK_TRAP live {} at op {}", self.live, self.ops.len()); }
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        i5::on_alloc(q.0, loc, self.live);
    }
    /// s825 adapter: append an already-remapped foreign op stream and its emitted Toffoli count.
    pub fn push_foreign(&mut self, ops: Vec<Op>, tof: u64) {
        assert!(self.rec.is_empty(), "foreign ops inside a recording");
        FSTART.with(|f| f.set(HMR_CNT.with(|c| c.get())));
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

/// I5-LANES owner-ledger probe (diagnostic only; inert unless I5_SNAP=<live threshold> is set): records, per
/// (profiler section, slot), the allocation sites of every live qubit at the first moment live >= threshold.
pub mod i5 {
    use std::cell::{Cell, RefCell};
    use std::collections::HashMap;
    use std::panic::Location;
    thread_local! {
        static ON: Cell<Option<u64>> = Cell::new(std::env::var("I5_SNAP").ok().and_then(|v| v.trim().parse().ok()));
        static OWN: RefCell<HashMap<u64, &'static Location<'static>>> = RefCell::new(HashMap::new());
        pub static SECT: Cell<&'static str> = Cell::new("-");
        pub static SLOT: Cell<i64> = Cell::new(-1);
        static SEEN: RefCell<HashMap<(&'static str, i64), u64>> = RefCell::new(HashMap::new());
        /// a1-ledger: register role of a live qubit (set by diagnostic hooks, dropped on free)
        static ROLE: RefCell<HashMap<u64, &'static str>> = RefCell::new(HashMap::new());
    }
    thread_local! {
        /// q792 diagnostic: ids of the running slot's LA / LB lanes (refreshed at every p3 section hook)
        static LALB: RefCell<HashMap<u64, &'static str>> = RefCell::new(HashMap::new());
    }
    /// q792 diagnostic: record the current LA / LB lane ids (no gates)
    pub fn set_lalb(la: &[crate::circuit::QubitId], lb: &[crate::circuit::QubitId]) {
        if ON.with(|c| c.get()).is_none() { return; }
        LALB.with(|r| { let mut r = r.borrow_mut(); r.clear();
            for q in la { r.insert(q.0, "LA*"); } for q in lb { r.insert(q.0, "LB*"); } });
    }
    /// a1-ledger diagnostic: tag live qubits with a register role (no gates)
    pub fn set_role(qs: &[crate::circuit::QubitId], role: &'static str) {
        if ON.with(|c| c.get()).is_none() { return; }
        ROLE.with(|r| { let mut r = r.borrow_mut(); for q in qs { r.insert(q.0, role); } });
    }
    pub fn set_sect(s: &'static str) { SECT.with(|c| c.set(s)); }
    pub fn set_slot(s: i64) { SLOT.with(|c| c.set(s)); }
    pub fn on_alloc(q: u64, loc: &'static Location<'static>, live: u64) {
        let Some(th) = ON.with(|c| c.get()) else { return };
        OWN.with(|o| { o.borrow_mut().insert(q, loc); });
        if live < th { return; }
        let key = (SECT.with(|c| c.get()), SLOT.with(|c| c.get()));
        let first = if std::env::var_os("I5_ALL").is_some() {
            // b793a diagnostic: one snapshot per (section, slot, triggering allocation line); inert unless I5_ALL is set
            thread_local! { static SEEN2: RefCell<std::collections::HashSet<(&'static str, i64, u32)>> = RefCell::new(Default::default()); }
            SEEN2.with(|s| s.borrow_mut().insert((key.0, key.1, loc.line())))
        } else { SEEN.with(|s| {
            let mut s = s.borrow_mut();
            let e = s.entry(key).or_insert(0);
            let f = live > *e;
            if f { *e = live; }
            f
        }) };
        if !first { return; }
        let mut h: HashMap<String, u64> = HashMap::new();
        OWN.with(|o| ROLE.with(|r| { let r = r.borrow(); for (q, l) in o.borrow().iter() {
            let k = match r.get(q) { Some(role) => format!("@{role}"), None => match LALB.with(|m| m.borrow().get(q).copied()) { Some(role) => format!("@{role}{}", l.line()), None => format!("{}:{}", l.file().rsplit('/').next().unwrap_or(""), l.line()) } };
            *h.entry(k).or_insert(0) += 1;
        } }));
        let mut v: Vec<_> = h.into_iter().collect();
        v.sort();
        let body: Vec<String> = v.iter().map(|(k, n)| format!("{k}={n}")).collect();
        eprintln!("I5SNAP sect={} slot={} live={} trig={} {}", key.0, key.1, live, loc.line(), body.join(" "));
        // b793b diagnostic (inert unless I5_IDS is set): ids per allocation site (ring / LA / LB lanes are not told apart by id here)
        if std::env::var_os("I5_IDS").is_some() {
            let mut ids: std::collections::BTreeMap<String, Vec<u64>> = Default::default();
            OWN.with(|o| for (q, l) in o.borrow().iter() { ids.entry(format!("{}", l.line())).or_default().push(*q); });
            let s: Vec<String> = ids.iter().filter(|(_, v)| v.len() <= 12).map(|(k, v)| { let mut v = v.clone(); v.sort(); format!("{k}:{v:?}") }).collect();
            eprintln!("I5IDS sect={} slot={} trig={} {}", key.0, key.1, loc.line(), s.join(" "));
        }
    }
    pub fn on_free(q: u64) {
        if ON.with(|c| c.get()).is_none() { return; }
        OWN.with(|o| { o.borrow_mut().remove(&q); });
        ROLE.with(|r| { r.borrow_mut().remove(&q); });
    }
}


// fable dev probe (inert unless FB_SPAN=<cap>): ops spent with live > cap, per section and slot, and the number of excursions
pub static FB_SPAN: std::sync::LazyLock<Option<u64>> = std::sync::LazyLock::new(|| std::env::var("FB_SPAN").ok().and_then(|v| v.trim().parse().ok()));
thread_local! {
    static FB_UP: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    static FB_ACC: std::cell::RefCell<std::collections::BTreeMap<String, (u64, u64, u64)>> = std::cell::RefCell::new(Default::default());
}
pub fn fb_span_up(live: u64, op: usize) {
    if let Some(c) = *FB_SPAN { if live == c + 1 { FB_UP.with(|u| u.set(Some(op))); } }
}
pub fn fb_span_down(live: u64, op: usize) {
    if let Some(c) = *FB_SPAN { if live == c { if let Some(o) = FB_UP.with(|u| u.take()) {
        let k = format!("{} s{}", i5::SECT.with(|c| c.get()), super::greedyfrog::p3_cur_slot());
        FB_ACC.with(|m| { let mut m = m.borrow_mut(); let e = m.entry(k).or_insert((0, 0, 0)); e.0 += 1; e.1 += (op - o) as u64; e.2 = e.2.max((op - o) as u64); });
    } } }
}
pub fn fb_span_dump() {
    FB_ACC.with(|m| for (k, (n, t, mx)) in m.borrow().iter() { eprintln!("FBSPAN {k} n={n} ops={t} max={mx}"); });
}
// P2-REBASE dev probe (inert unless P2_OVER=<cap> is set): allocation sites that push live above the cap
pub static P2_OVER: std::sync::LazyLock<Option<u64>> = std::sync::LazyLock::new(|| std::env::var("P2_OVER").ok().and_then(|v| v.trim().parse().ok()));
thread_local! { static P2_SITES: std::cell::RefCell<std::collections::BTreeMap<String, (u64, u64, usize, usize)>> = std::cell::RefCell::new(Default::default()); }
fn p2_over_note(live: u64) {
    let bt = std::backtrace::Backtrace::force_capture().to_string();
    let site: Vec<String> = bt.lines().filter(|l| l.contains("at ./src") || l.contains("at src") || l.contains("point_add/")).filter(|l| !l.contains("builder.rs")).take(3).map(|l| l.trim().rsplit('/').next().unwrap_or("").to_string()).collect();
    let k = site.join(" < ");
    let sl = super::greedyfrog::p3_cur_slot();
    P2_SITES.with(|m| { let mut m = m.borrow_mut(); let e = m.entry(k).or_insert((0, 0, usize::MAX, 0)); e.0 += 1; e.1 = e.1.max(live); e.2 = e.2.min(sl); e.3 = e.3.max(sl); });
}
pub fn p2_over_dump() {
    fb_span_dump();
    OVER_LOC.with(|m| for (k, n) in m.borrow().iter() { eprintln!("OVERLOC {n} {k}"); });
    P2_SITES.with(|m| for (k, (n, l, a, z)) in m.borrow().iter() { eprintln!("P2_OVER live<={l} n={n} slots {a}-{z} {k}"); });
}

/// R8-ROOM0 dev instrument (inert unless R8_IDLE is set): live lanes never touched since their allocation (|0>), and a
/// tally of their allocation sites at the moments a pass is short of clean lanes
pub mod r8idle {
    use crate::circuit::QubitId;
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::panic::Location;
    pub static ON: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R8_IDLE").is_some());
    thread_local! {
        pub static IDLE: RefCell<BTreeMap<u64, &'static Location<'static>>> = RefCell::new(BTreeMap::new());
        static TALLY: RefCell<BTreeMap<String, (u64, u64)>> = RefCell::new(BTreeMap::new());
    }
    pub fn touch(qs: &[QubitId]) {
        IDLE.with(|m| { let mut m = m.borrow_mut(); for q in qs { m.remove(&q.0); } });
    }
    #[track_caller]
    pub fn note(tag: &str, short: u64) {
        if !*ON || short == 0 { return; }
        let at = Location::caller();
        IDLE.with(|m| for l in m.borrow().values() {
            let k = format!("{tag}@{}:{} idle {}:{}", at.file().rsplit('/').next().unwrap(), at.line(), l.file().rsplit('/').next().unwrap(), l.line());
            TALLY.with(|t| { let mut t = t.borrow_mut(); let e = t.entry(k).or_insert((0, 0)); e.0 += 1; e.1 += short; });
        });
    }
    thread_local! {
        static PEND: RefCell<Vec<(String, Vec<u64>, Vec<(u64, &'static Location<'static>)>, u64)>> = RefCell::new(vec![]);
    }
    /// a short pool: its lanes, the lanes idle now; resolved when the first pool lane is freed (lanes still idle then
    /// were idle through the pool's whole life)
    #[track_caller]
    pub fn pend(tag: &str, pool: &[QubitId], short: u64) {
        if !*ON || short == 0 || pool.is_empty() { return; }
        let at = Location::caller();
        let snap: Vec<(u64, &'static Location<'static>)> = IDLE.with(|m| m.borrow().iter().map(|(k, v)| (*k, *v)).collect());
        PEND.with(|p| p.borrow_mut().push((format!("{tag}@{}:{}", at.file().rsplit('/').next().unwrap(), at.line()), pool.iter().map(|q| q.0).collect(), snap, short)));
    }
    pub fn resolve(q: u64) {
        let hit: Vec<_> = PEND.with(|p| {
            let mut p = p.borrow_mut();
            let (h, k): (Vec<_>, Vec<_>) = std::mem::take(&mut *p).into_iter().partition(|e| e.1.contains(&q));
            *p = k;
            h
        });
        for (key, _, snap, short) in hit {
            IDLE.with(|m| { let m = m.borrow(); for (id, l) in snap {
                if m.get(&id).is_some_and(|x| std::ptr::eq(*x, l)) {
                    let k = format!("{key} idle-through {}:{}", l.file().rsplit('/').next().unwrap(), l.line());
                    TALLY.with(|t| { let mut t = t.borrow_mut(); let e = t.entry(k).or_insert((0, 0)); e.0 += 1; e.1 += short; });
                }
            }});
        }
    }
    pub fn dump() {
        TALLY.with(|t| for (k, (n, s)) in t.borrow().iter() { eprintln!("R8IDLE {n} {s} {k}"); });
    }
}

pub static HMR_TRAP: std::sync::LazyLock<Option<u64>> = std::sync::LazyLock::new(|| std::env::var("HMR_TRAP").ok().and_then(|v| v.trim().parse().ok()));
thread_local! { static HMR_CNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) }; static FSTART: std::cell::Cell<u64> = const { std::cell::Cell::new(0) }; }
pub static PEAK_TRAP: std::sync::LazyLock<u64> = std::sync::LazyLock::new(|| std::env::var("PEAK_TRAP").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(u64::MAX));

thread_local! { static OVER_LOC: std::cell::RefCell<std::collections::BTreeMap<String,u64>> = std::cell::RefCell::new(Default::default()); }

pub static R10TRK: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R10_TRACK").is_some());
thread_local! { pub static R10LOC: std::cell::RefCell<std::collections::BTreeMap<u64, String>> = std::cell::RefCell::new(Default::default()); }
/// R10 dev: live lanes allocated after `from` (id order) with their allocation sites
pub fn r10_dump(tag: &str) {
    R10LOC.with(|m| { let m = m.borrow(); let mut c: std::collections::BTreeMap<String, Vec<u64>> = Default::default();
        for (q, l) in m.iter() { c.entry(l.clone()).or_default().push(*q); }
        for (l, qs) in c { eprintln!("R10LIVE {tag} {l} n={} {:?}", qs.len(), &qs[..qs.len().min(8)]); } });
}
