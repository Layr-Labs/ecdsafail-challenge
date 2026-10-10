//! Builder: qubit pool, op emission and a small gate IR that can be emitted forward or inverted.
//!
//! Gates are always emitted through `g()`. While a recording is open, they go to the recording instead of the
//! op stream; `play(rec, inverse)` emits a recording forward or as its exact inverse. Measurement-based
//! pairs include `AndC` (Toffoli into a fresh |0> target, 1 Toffoli) and `AndU`
//! (X-basis measurement of the target plus a classically conditioned CZ fix-up, 0 Toffoli). They invert into
//! each other. `CarryC` computes a carry flag; `CarryU` measures it away and
//! invokes a phase oracle only under the captured classical measurement bit.

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT, NO_REG};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
struct ChunkDebts {
    width: usize,
    flagged: bool,
    incoming: bool,
    count: usize,
    debts: Option<Vec<super::chunked::Debt>>,
}

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
    CarryC(usize),
    CarryU(usize),
    /// target ^= AND(lits) computed coherently (temporary-AND chain on clean temps).
    MbuC(usize),
    /// target = AND(lits) -> |0> by X measurement; the AND's phase oracle runs only when the outcome is 1.
    MbuU(usize),
    /// target ^= XOR(linear, quadratic monomials), with target initially |0>.
    QuadC(usize),
    /// Measurement-uncompute the same degree-at-most-two Boolean polynomial.
    QuadU(usize),
    ChunkC(usize),
    ChunkU(usize),
}

#[derive(Clone)]
struct MbuCall {
    target: QubitId,
    lits: Vec<(QubitId, bool)>,
    temps: Vec<QubitId>,
}

#[derive(Clone)]
struct QuadCall {
    target: QubitId,
    linear: Vec<QubitId>,
    pairs: Vec<(QubitId, QubitId)>,
}

#[derive(Clone)]
struct CarryCall {
    a: Vec<QubitId>,
    t: Vec<QubitId>,
    ctl: QubitId,
    flag: QubitId,
    pool: Vec<QubitId>,
    cin: Option<QubitId>,
}

pub struct B {
    pub ops: Vec<Op>,
    carry_calls: Vec<CarryCall>,
    chunk_calls: Vec<super::chunked::Call>,
    mbu_calls: Vec<MbuCall>,
    quad_calls: Vec<QuadCall>,
    /// Toffolis emitted inside classical conditions (executed with probability 1/2 each)
    pub tof_cond: u64,
    cond_depth: u32,
    next_q: u64,
    free_q: BTreeSet<u64>,
    pub live: u64,
    pub peak: u64,
    bit: BitId,
    rec: Vec<Vec<G>>,
    pub tof: u64,
    pub peak_op: usize,
    next_bit: u64,
    next_division: usize,
    chunk_debts: BTreeMap<super::chunked::PairKey, ChunkDebts>,
}

impl B {
    pub fn new() -> Self {
        let mut b = B {
            ops: Vec::new(),
            carry_calls: Vec::new(),
            chunk_calls: Vec::new(),
            mbu_calls: Vec::new(),
            quad_calls: Vec::new(),
            tof_cond: 0,
            cond_depth: 0,
            next_q: 0,
            free_q: BTreeSet::new(),
            live: 0,
            peak: 0,
            bit: NO_BIT,
            rec: Vec::new(),
            tof: 0,
            next_bit: 10_000,
            peak_op: 0,
            next_division: 0,
            chunk_debts: BTreeMap::new(),
        };
        b.bit = BitId(0);
        b
    }

    // ---------------------------------------------------------------- qubits
    pub fn alloc(&mut self) -> QubitId {
        let id = if let Some(&q) = self.free_q.iter().next() {
            self.free_q.remove(&q);
            q
        } else {
            self.next_q += 1;
            self.next_q - 1
        };
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        QubitId(id)
    }
    pub fn alloc_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.alloc()).collect()
    }
    /// Release a qubit that is |0> on every shot.
    pub fn free(&mut self, q: QubitId) {
        assert!(self.rec.is_empty(), "free inside a recording");
        assert!(self.free_q.insert(q.0), "double free q{}", q.0);
        self.live -= 1;
    }
    pub fn free_n(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    pub fn width(&self) -> u64 {
        self.next_q
    }

    // ---------------------------------------------------------------- registers
    pub fn declare_qubits(&mut self, reg: u64, qs: &[QubitId]) {
        self.raw(Op {
            kind: OperationType::Register,
            r_target: RegisterId(reg),
            ..Op::empty()
        });
        for &q in qs {
            self.raw(Op {
                kind: OperationType::AppendToRegister,
                q_target: q,
                r_target: RegisterId(reg),
                ..Op::empty()
            });
        }
    }
    pub fn declare_bits(&mut self, reg: u64, n: usize) -> Vec<BitId> {
        self.raw(Op {
            kind: OperationType::Register,
            r_target: RegisterId(reg),
            ..Op::empty()
        });
        let bs: Vec<BitId> = (0..n).map(|i| BitId(1 + reg * 1000 + i as u64)).collect();
        for &b in &bs {
            self.raw(Op {
                kind: OperationType::AppendToRegister,
                c_target: b,
                r_target: RegisterId(reg),
                ..Op::empty()
            });
        }
        bs
    }

    // ---------------------------------------------------------------- emission
    fn raw(&mut self, op: Op) {
        match op.kind {
            OperationType::PushCondition => self.cond_depth += 1,
            OperationType::PopCondition => self.cond_depth -= 1,
            OperationType::CCX | OperationType::CCZ if self.cond_depth > 0 => self.tof_cond += 1,
            _ => {}
        }
        debug_assert!({
            op.validate();
            true
        });
        let _ = NO_REG;
        self.ops.push(op);
    }
    fn emit(&mut self, g: G, inverse: bool) {
        let e = |kind, t: QubitId, c1: QubitId, c2: QubitId| Op {
            kind,
            q_target: t,
            q_control1: c1,
            q_control2: c2,
            ..Op::empty()
        };
        match g {
            G::X(t) => self.raw(e(OperationType::X, t, NO_QUBIT, NO_QUBIT)),
            G::Cx(c, t) => self.raw(e(OperationType::CX, t, c, NO_QUBIT)),
            G::Cz(a, b) => self.raw(e(OperationType::CZ, b, a, NO_QUBIT)),
            G::Swap(a, b) => self.raw(e(OperationType::Swap, b, a, NO_QUBIT)),
            G::Ccx(a, b, t) => {
                self.tof += 1;
                self.raw(e(OperationType::CCX, t, a, b))
            }
            G::XIf(t, c) => self.raw(Op {
                kind: OperationType::X,
                q_target: t,
                c_condition: c,
                ..Op::empty()
            }),
            G::ZIf(t, c) => self.raw(Op {
                kind: OperationType::Z,
                q_target: t,
                c_condition: c,
                ..Op::empty()
            }),
            G::ChunkC(i) | G::ChunkU(i) => {
                let call = self.chunk_calls[i].clone();
                let subtract = matches!(g, G::ChunkU(_)) != inverse;
                super::chunked::apply(self, &call, subtract);
            }
            G::CarryC(i) | G::CarryU(i) => {
                let call = self.carry_calls[i].clone();
                let compute = matches!(g, G::CarryC(_)) != inverse;
                if !compute {
                    let m = self.bit;
                    self.raw(Op {
                        kind: OperationType::Hmr,
                        q_target: call.flag,
                        c_target: m,
                        ..Op::empty()
                    });
                    // Push snapshots m before the inner temporary-AND measurements reuse bit 0.
                    self.raw(Op {
                        kind: OperationType::PushCondition,
                        c_condition: m,
                        ..Op::empty()
                    });
                }
                self.carry_call(&call, !compute);
                if !compute {
                    self.raw(Op {
                        kind: OperationType::PopCondition,
                        ..Op::empty()
                    });
                }
            }
            G::MbuC(i) | G::MbuU(i) => {
                let call = self.mbu_calls[i].clone();
                let compute = matches!(g, G::MbuC(_)) != inverse;
                self.mbu_call(&call, compute);
            }
            G::QuadC(i) | G::QuadU(i) => {
                let call = self.quad_calls[i].clone();
                let compute = matches!(g, G::QuadC(_)) != inverse;
                self.quad_call(&call, compute);
            }
            G::AndC(a, b, t) | G::AndU(a, b, t) => {
                let compute = matches!(g, G::AndC(..)) != inverse;
                if compute {
                    self.tof += 1;
                    self.raw(e(OperationType::CCX, t, a, b));
                } else {
                    let m = self.bit;
                    self.raw(Op {
                        kind: OperationType::Hmr,
                        q_target: t,
                        c_target: m,
                        ..Op::empty()
                    });
                    self.raw(Op {
                        kind: OperationType::CZ,
                        q_target: b,
                        q_control1: a,
                        c_condition: m,
                        ..Op::empty()
                    });
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
    /// Profiling: expected executed Toffoli of `r` played forward or inverted (emitted and dropped again; the
    /// open recordings are untouched).
    pub fn measure(&mut self, r: &[G], inverse: bool) -> f64 {
        let debts = self.chunk_debts.clone();
        let next_bit = self.next_bit;
        let saved = std::mem::take(&mut self.rec);
        let (n0, tof, tc, cd) = (self.ops.len(), self.tof, self.tof_cond, self.cond_depth);
        self.play(r, inverse);
        let mut w = 1.0f64;
        let mut st = vec![];
        let mut tot = 0.0;
        for op in &self.ops[n0..] {
            use crate::circuit::OperationType as K;
            match op.kind {
                K::PushCondition => {
                    st.push(w);
                    w *= 0.5;
                }
                K::PopCondition => w = st.pop().unwrap(),
                K::CCX | K::CCZ => tot += w,
                _ => {}
            }
        }
        self.ops.truncate(n0);
        (self.tof, self.tof_cond, self.cond_depth) = (tof, tc, cd);
        self.rec = saved;
        self.chunk_debts = debts;
        self.next_bit = next_bit;
        tot
    }
    /// Emit a recording forward or as its inverse (into the enclosing recording if one is open).
    pub fn play(&mut self, r: &[G], inverse: bool) {
        if inverse {
            for &g in r.iter().rev() {
                let gi = match g {
                    G::AndC(a, b, t) => G::AndU(a, b, t),
                    G::AndU(a, b, t) => G::AndC(a, b, t),
                    G::CarryC(i) => G::CarryU(i),
                    G::CarryU(i) => G::CarryC(i),
                    G::MbuC(i) => G::MbuU(i),
                    G::MbuU(i) => G::MbuC(i),
                    G::QuadC(i) => G::QuadU(i),
                    G::QuadU(i) => G::QuadC(i),
                    G::ChunkC(i) => G::ChunkU(i),
                    G::ChunkU(i) => G::ChunkC(i),
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

    /// Uncompute a known carry flag by X measurement and a classically gated
    /// phase oracle. Reversing a recording computes the same flag coherently.
    pub fn carry_erase(
        &mut self,
        a: &[QubitId],
        t: &[QubitId],
        ctl: QubitId,
        flag: QubitId,
        pool: &[QubitId],
    ) {
        self.carry_erase_cin(a, t, ctl, flag, pool, None);
    }
    /// carry_erase with a carry-in qubit (`cin`, outside a and t): flag = ctl & carry_out(a + t + cin).
    pub fn carry_erase_cin(
        &mut self,
        a: &[QubitId],
        t: &[QubitId],
        ctl: QubitId,
        flag: QubitId,
        pool: &[QubitId],
        cin: Option<QubitId>,
    ) {
        assert_eq!(a.len(), t.len());
        assert!(pool.len() >= a.len());
        let id = self.carry_calls.len();
        self.carry_calls.push(CarryCall {
            a: a.to_vec(),
            t: t.to_vec(),
            ctl,
            flag,
            pool: pool[..a.len()].to_vec(),
            cin,
        });
        self.g(G::CarryU(id));
    }
    fn mbu_spec(&mut self, target: QubitId, lits: &[(QubitId, bool)], temps: &[QubitId]) -> usize {
        let n = lits.len();
        assert!(n >= 1 && temps.len() + 2 >= n, "mbu: {} literals need {} temps", n, n.saturating_sub(2));
        self.mbu_calls.push(MbuCall {
            target,
            lits: lits.to_vec(),
            temps: temps[..n.saturating_sub(2)].to_vec(),
        });
        self.mbu_calls.len() - 1
    }
    /// target ^= AND(lits) (target |0> before), coherent; the inverse of `mbu_erase`. n - 1 Toffoli.
    pub fn mbu_compute(&mut self, target: QubitId, lits: &[(QubitId, bool)], temps: &[QubitId]) {
        let id = self.mbu_spec(target, lits, temps);
        self.g(G::MbuC(id));
    }
    /// target (= AND(lits)) -> |0>: X measurement, then the AND's phase oracle (n - 2 Toffoli) under the outcome.
    pub fn mbu_erase(&mut self, target: QubitId, lits: &[(QubitId, bool)], temps: &[QubitId]) {
        let id = self.mbu_spec(target, lits, temps);
        self.g(G::MbuU(id));
    }

    fn quad_spec(&mut self, target: QubitId, linear: &[QubitId], pairs: &[(QubitId, QubitId)]) -> usize {
        assert!(linear.iter().all(|&q| q != target));
        assert!(pairs.iter().all(|&(a, b)| a != target && b != target && a != b));
        self.quad_calls.push(QuadCall { target, linear: linear.to_vec(), pairs: pairs.to_vec() });
        self.quad_calls.len() - 1
    }

    /// Coherently compute a degree-at-most-two Boolean polynomial into a clean target.
    pub fn quad_compute(&mut self, target: QubitId, linear: &[QubitId], pairs: &[(QubitId, QubitId)]) {
        let id = self.quad_spec(target, linear, pairs);
        self.g(G::QuadC(id));
    }

    /// X-measure a target holding a degree-at-most-two Boolean polynomial and apply its exact
    /// diagonal phase correction. The correction contains only Z/CZ and therefore no Toffoli.
    pub fn quad_erase(&mut self, target: QubitId, linear: &[QubitId], pairs: &[(QubitId, QubitId)]) {
        let id = self.quad_spec(target, linear, pairs);
        self.g(G::QuadU(id));
    }

    fn quad_call(&mut self, c: &QuadCall, compute: bool) {
        if compute {
            for &q in &c.linear {
                self.cx(q, c.target);
            }
            for &(a, b) in &c.pairs {
                self.ccx(a, b, c.target);
            }
            return;
        }
        let m = self.bit;
        self.raw(Op { kind: OperationType::Hmr, q_target: c.target, c_target: m, ..Op::empty() });
        self.raw(Op { kind: OperationType::PushCondition, c_condition: m, ..Op::empty() });
        for &q in &c.linear {
            self.raw(Op { kind: OperationType::Z, q_target: q, ..Op::empty() });
        }
        for &(a, b) in &c.pairs {
            self.cz(a, b);
        }
        self.raw(Op { kind: OperationType::PopCondition, ..Op::empty() });
    }
    fn mbu_call(&mut self, c: &MbuCall, compute: bool) {
        let n = c.lits.len();
        if !compute {
            let m = self.bit;
            self.raw(Op {
                kind: OperationType::Hmr,
                q_target: c.target,
                c_target: m,
                ..Op::empty()
            });
            self.raw(Op {
                kind: OperationType::PushCondition,
                c_condition: m,
                ..Op::empty()
            });
        }
        for &(q, ng) in &c.lits {
            if ng {
                self.x(q);
            }
        }
        let l: Vec<QubitId> = c.lits.iter().map(|x| x.0).collect();
        // chain over the first k literals into temps; returns the qubit holding their AND
        let k = if compute { n - 1 } else { n - 1 };
        let mut acc = l[0];
        let mut used = vec![];
        for i in 1..k {
            let t = c.temps[i - 1];
            self.and_c(acc, l[i], t);
            used.push((acc, l[i], t));
            acc = t;
        }
        if compute {
            if n == 1 {
                self.cx(l[0], c.target);
            } else {
                self.ccx(acc, l[n - 1], c.target);
            }
        } else if n == 1 {
            self.raw(Op {
                kind: OperationType::Z,
                q_target: l[0],
                ..Op::empty()
            });
        } else {
            self.cz(acc, l[n - 1]);
        }
        for &(a, b2, t) in used.iter().rev() {
            self.and_u(a, b2, t);
        }
        for &(q, ng) in &c.lits {
            if ng {
                self.x(q);
            }
        }
        if !compute {
            self.raw(Op {
                kind: OperationType::PopCondition,
                ..Op::empty()
            });
        }
    }

    fn carry_call(&mut self, spec: &CarryCall, phase: bool) {
        let (a, t, pool) = (&spec.a, &spec.t, &spec.pool);
        let n = a.len();
        let cin = |i: usize| if i == 0 { spec.cin } else { Some(pool[i - 1]) };
        for i in 0..n {
            match cin(i) {
                None => self.and_c(a[0], t[0], pool[0]),
                Some(ci) => {
                    self.cx(ci, a[i]);
                    self.cx(ci, t[i]);
                    self.and_c(a[i], t[i], pool[i]);
                    self.cx(ci, pool[i]);
                }
            }
        }
        if phase {
            self.cz(spec.ctl, pool[n - 1]);
        } else {
            self.ccx(spec.ctl, pool[n - 1], spec.flag);
        }
        for i in (0..n).rev() {
            match cin(i) {
                None => self.and_u(a[0], t[0], pool[0]),
                Some(ci) => {
                    self.cx(ci, pool[i]);
                    self.and_u(a[i], t[i], pool[i]);
                    self.cx(ci, t[i]);
                    self.cx(ci, a[i]);
                }
            }
        }
    }

    pub fn chunk_add(&mut self, call: super::chunked::Call) {
        let id = self.chunk_calls.len();
        self.chunk_calls.push(call);
        self.g(G::ChunkC(id));
    }
    pub fn new_division(&mut self) -> usize {
        let id = self.next_division;
        self.next_division += 1;
        id
    }
    pub fn save_chunk_debts(&mut self, key: super::chunked::PairKey, width: usize, flagged: bool, incoming: bool, debts: Vec<super::chunked::Debt>) {
        let count = debts.len();
        assert!(self.chunk_debts.insert(key, ChunkDebts { width, flagged, incoming, count, debts: Some(debts) }).is_none(), "duplicate forward semantic add {key:?}");
    }
    pub fn has_chunk_debts(&self, key: super::chunked::PairKey) -> bool {
        self.chunk_debts.contains_key(&key)
    }
    pub fn take_chunk_debts(&mut self, key: super::chunked::PairKey, width: usize, flagged: bool, incoming: bool) -> Vec<super::chunked::Debt> {
        let d = self.chunk_debts.get_mut(&key).expect("missing paired forward add");
        assert_eq!((d.width, d.flagged, d.incoming), (width, flagged, incoming), "semantic add shape changed {key:?}");
        d.debts.take().expect("paired receipt consumed twice")
    }
    pub fn close_division(&mut self, division: usize) -> usize {
        let keys: Vec<_> = self.chunk_debts.keys().filter(|k| k.division == division).copied().collect();
        let count: usize = keys.iter().map(|k| self.chunk_debts[k].count).sum();
        for key in &keys {
            assert!(self.chunk_debts[key].debts.is_none(), "unconsumed forward add {key:?}");
            self.chunk_debts.remove(key);
        }
        eprintln!("DEFERRED_CARRY division={division} closed_adds={} closed_receipts={count}", keys.len());
        keys.len()
    }
    pub fn measure_and_push(&mut self, q: QubitId) {
        assert!(self.rec.is_empty());
        self.raw(Op {
            kind: OperationType::Hmr,
            q_target: q,
            c_target: self.bit,
            ..Op::empty()
        });
        self.raw(Op {
            kind: OperationType::PushCondition,
            c_condition: self.bit,
            ..Op::empty()
        });
    }
    pub fn pop_classical(&mut self) {
        self.raw(Op {
            kind: OperationType::PopCondition,
            ..Op::empty()
        });
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
    /// X-basis measurement of q into classical bit c (q -> |0>). Not invertible; never inside a recording.
    pub fn hmr_to(&mut self, q: QubitId, c: BitId) {
        assert!(self.rec.is_empty());
        self.raw(Op {
            kind: OperationType::Hmr,
            q_target: q,
            c_condition: NO_BIT,
            c_target: c,
            ..Op::empty()
        });
    }
    /// Take a specific free qubit back out of the pool.
    pub fn acquire(&mut self, q: QubitId) {
        assert!(self.free_q.remove(&q.0), "acquire of a busy qubit q{}", q.0);
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
    }
    pub fn fresh_bits(&mut self, n: usize) -> Vec<BitId> {
        let v: Vec<BitId> = (0..n).map(|i| BitId(self.next_bit + i as u64)).collect();
        self.next_bit += n as u64;
        v
    }
    /// Import a closed square block by relabeling its actual quantum and
    /// classical lanes. Its input ABI is local out[0..256], y[256..512].
    /// Scratch is allocated through this builder, and returned only after
    /// the block's complete inverse has cleared it.
    pub fn native_square(&mut self, out: &[QubitId], y: &[QubitId]) {
        assert!(self.rec.is_empty() && self.cond_depth == 0);
        assert_eq!(out.len(), 256); assert_eq!(y.len(), 256);
        assert_eq!(self.live, 512, "native square requires exactly two live coordinates");
        let ops = super::super::public_square_port::native_square_ops();
        let (nq, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
        assert!(nq <= 975 && nq >= 512);
        let scratch = self.alloc_n(nq as usize - 512);
        let mut qm = out.to_vec(); qm.extend_from_slice(y); qm.extend_from_slice(&scratch);
        let cm = self.fresh_bits(nb as usize);
        for mut op in ops {
            assert_eq!(op.r_target, NO_REG, "square block must have no register declarations");
            for q in [&mut op.q_target, &mut op.q_control1, &mut op.q_control2] {
                if *q != NO_QUBIT { *q = qm[q.0 as usize]; }
            }
            for c in [&mut op.c_target, &mut op.c_condition] {
                if *c != NO_BIT { *c = cm[c.0 as usize]; }
            }
            if matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
                self.tof += 1;
                assert!(self.cond_depth <= 1, "native square accounting needs depth-one conditions");
                assert_eq!(op.c_condition, NO_BIT, "directly conditioned Toffoli requires separate accounting");
            }
            self.raw(op);
        }
        assert_eq!(self.cond_depth, 0);
        self.free_n(&scratch);
    }
    /// Emit a recording controlled on `c`: every gate gets the extra control, except AND compute/uncompute pairs
    /// (their target is clean on both sides whatever happens in between). `tmp` = clean helper not in `r`.
    pub fn play_ctrl(&mut self, r: &[G], c: QubitId, tmp: QubitId) {
        for &g in r {
            match g {
                G::X(t) => self.cx(c, t),
                G::Cx(a, t) => self.ccx(c, a, t),
                G::Ccx(a, b2, t) => {
                    self.and_c(c, a, tmp);
                    self.ccx(tmp, b2, t);
                    self.and_u(c, a, tmp);
                }
                G::Swap(a, b2) => self.cswap(c, a, b2),
                G::AndC(..) | G::AndU(..) => self.g(g),
                other => panic!("play_ctrl: unsupported gate {:?}", other),
            }
        }
    }
    /// play_ctrl with the AND pairs controlled too (AND compute and uncompute both become controlled Toffolis):
    /// exact identity on control-0 shots whatever the recording's AND nesting.
    pub fn play_ctrl_full(&mut self, r: &[G], c: QubitId, tmp: QubitId) {
        for &g in r {
            match g {
                G::X(t) => self.cx(c, t),
                G::Cx(a, t) => self.ccx(c, a, t),
                G::Ccx(a, b2, t) | G::AndC(a, b2, t) | G::AndU(a, b2, t) => {
                    self.and_c(c, a, tmp);
                    self.ccx(tmp, b2, t);
                    self.and_u(c, a, tmp);
                }
                G::Swap(a, b2) => self.cswap(c, a, b2),
                other => panic!("play_ctrl_full: unsupported gate {:?}", other),
            }
        }
    }
    /// Controlled swap (Fredkin), 1 Toffoli.
    pub fn cswap(&mut self, c: QubitId, a: QubitId, b: QubitId) {
        self.cx(b, a);
        self.ccx(c, a, b);
        self.cx(b, a);
    }
}
