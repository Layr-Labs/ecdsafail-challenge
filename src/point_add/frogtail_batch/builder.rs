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

/// Source of one addend lane of a classical (in-circuit, 0-T) ripple add.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CSrc {
    Zero,
    One,
    Bit(BitId),
}

/// Sentinel constant-|1> control used by Lilypad-G's unconditional signed
/// adds. Gate helpers lower it to X/CX, and it must never reach the gate IR.
pub const ONE: QubitId = QubitId(u64::MAX - 7);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G {
    Neg,
    Ccz(QubitId,QubitId,QubitId),
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
    CmpC(usize),
    CmpU(usize),
    ChunkC(usize),
    ChunkU(usize),
    /// Lane cloud-lily852: ANF chart XORed into a clean target (compute) / X-measure erase with its phase oracle.
    AnfC(usize),
    AnfU(usize),
    /// Lane cloud-lily852: the chart's phase oracle under a classical bit (self-inverse).
    AnfP(usize),
    CircuitC(usize), CircuitU(usize), CircuitP(usize),
}

/// Lane cloud-lily852: a chart's monomials (qubit sets) after the rho fold.
#[derive(Clone)]
pub(crate) struct AnfCall {
    pub affine: Vec<(QubitId, QubitId, QubitId)>,
    pub clean: Vec<QubitId>,
    pub fold: Vec<QubitId>,
    pub flip: bool,
    pub terms: Vec<Vec<QubitId>>,
    pub target: QubitId,
    pub dirty: Vec<QubitId>,
    pub cond: BitId,
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
struct CmpCall { u:Vec<QubitId>, k:u64, target:QubitId, temps:Vec<QubitId> }

#[cfg(test)]
thread_local! {static TEST_CMP_MBU:std::cell::Cell<bool>=const{std::cell::Cell::new(true)};}
#[cfg(test)]
pub(crate) fn test_cmp_mbu(v:bool){TEST_CMP_MBU.with(|c|c.set(v));}
fn cmp_mbu_enabled()->bool {
    #[cfg(test)] {return TEST_CMP_MBU.with(|c|c.get());}
    #[cfg(not(test))] {true}
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

#[derive(Clone)]
struct CircuitChart {compute:Vec<G>,phase:Vec<G>,target:QubitId,cond:BitId}

pub struct B {
    pub ops: Vec<Op>,
    pub low_clean: Vec<QubitId>,
    carry_calls: Vec<CarryCall>,
    chunk_calls: Vec<super::chunked::Call>,
    mbu_calls: Vec<MbuCall>,
    quad_calls: Vec<QuadCall>,
    cmp_calls: Vec<CmpCall>,
    anf_calls: Vec<AnfCall>,
    circuit_charts: Vec<CircuitChart>,
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
            low_clean: Vec::new(),
            carry_calls: Vec::new(),
            chunk_calls: Vec::new(),
            mbu_calls: Vec::new(),
            quad_calls: Vec::new(),
            cmp_calls: Vec::new(),
            anf_calls: Vec::new(),
            circuit_charts: Vec::new(),
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
        if matches!(op.kind, OperationType::CCX|OperationType::CCZ) && (op.q_target==op.q_control1 || op.q_target==op.q_control2 || op.q_control1==op.q_control2) {panic!("ALIASED OP at {} {:?}",self.ops.len(),op);}
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
            G::Neg => self.raw(Op{kind:OperationType::Neg,..Op::empty()}),
            G::Ccz(a,c,t) => {self.tof+=1;self.raw(e(OperationType::CCZ,t,c,a));},
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
            G::CmpC(i) | G::CmpU(i) => {
                let call=self.cmp_calls[i].clone();
                self.cmp_call(&call,matches!(g,G::CmpC(_))!=inverse);
            }
            G::QuadC(i) | G::QuadU(i) => {
                let call = self.quad_calls[i].clone();
                let compute = matches!(g, G::QuadC(_)) != inverse;
                self.quad_call(&call, compute);
            }
            G::CircuitC(i)|G::CircuitU(i)|G::CircuitP(i)=>{
                let c=self.circuit_charts[i].clone();
                let mode=match g{G::CircuitP(_)=>2,G::CircuitC(_)=>u8::from(inverse),_=>u8::from(!inverse)};
                if mode==0 {self.play(&c.compute,false);}else{
                    if mode==1 {self.measure_and_push(c.target);}else{self.raw(Op{kind:OperationType::PushCondition,c_condition:c.cond,..Op::empty()});}
                    self.play(&c.phase,false);self.pop_classical();
                }
            }
            G::AnfC(i) | G::AnfU(i) | G::AnfP(i) => {
                let call = self.anf_calls[i].clone();
                let mode = match g { G::AnfP(_) => 2, G::AnfC(_) => u8::from(inverse), _ => u8::from(!inverse) };
                self.anf_call(&call, mode);
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
        match g {
            G::X(a) | G::Cx(a, _) | G::Cz(a, _) | G::Swap(a, _) => assert!(a != ONE),
            _ => {}
        }
        match g {
            G::Cx(_, a) | G::Cz(_, a) | G::Swap(_, a) => assert!(a != ONE),
            G::Ccx(a, b, c) | G::AndC(a, b, c) | G::AndU(a, b, c) => {
                assert!(a != ONE && b != ONE && c != ONE)
            }
            _ => {}
        }
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
        // Primitive recordings have no receipt effects or nested conditions.
        // Count them directly; the general path below handles symbolic calls.
        let primitive=r.iter().try_fold(0u64,|sum,g|Some(sum+match *g {
            G::Ccx(..)|G::Ccz(..)=>1,
            G::AndC(..)=>u64::from(!inverse),G::AndU(..)=>u64::from(inverse),
            G::Neg|G::X(..)|G::Cx(..)|G::Cz(..)|G::Swap(..)|G::XIf(..)|G::ZIf(..)=>0,
            _=>return None,
        }));
        if let Some(cost)=primitive{return cost as f64;}
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
                    G::CmpC(i) => G::CmpU(i),
                    G::CmpU(i) => G::CmpC(i),
                    G::QuadC(i) => G::QuadU(i),
                    G::QuadU(i) => G::QuadC(i),
                    G::ChunkC(i) => G::ChunkU(i),
                    G::ChunkU(i) => G::ChunkC(i),
                    G::CircuitC(i)=>G::CircuitU(i),
                    G::CircuitU(i)=>G::CircuitC(i),
                    G::AnfC(i) => G::AnfU(i),
                    G::AnfU(i) => G::AnfC(i),
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
        // retake799: with ctl = ONE the last carry is never put on a lane, so n - 1 pool lanes suffice
        assert!(pool.len() >= a.len() || (2 * pool.len() >= a.len() + 1 && a.len() >= 3),
                "carry erase: pool {} for {} lanes", pool.len(), a.len());
        let id = self.carry_calls.len();
        self.carry_calls.push(CarryCall {
            a: a.to_vec(),
            t: t.to_vec(),
            ctl,
            flag,
            pool: pool[..a.len().min(pool.len())].to_vec(),
            cin,
        });
        self.g(G::CarryU(id));
    }
    fn cmp_spec(&mut self,u:&[QubitId],k:u64,target:QubitId,temps:&[QubitId])->usize {
        assert!(!u.is_empty() && u.len()<64 && k>0 && k<=1u64<<u.len());
        assert!(temps.len()>=u.len().saturating_sub(1));
        assert!(!u.contains(&target) && !temps.contains(&target));
        assert!(temps.iter().all(|q|!u.contains(q)));
        self.cmp_calls.push(CmpCall{u:u.to_vec(),k,target,temps:temps.to_vec()});
        self.cmp_calls.len()-1
    }
    pub fn cmp_compute(&mut self,u:&[QubitId],k:u64,target:QubitId,temps:&[QubitId]) {
        let i=self.cmp_spec(u,k,target,temps);self.g(G::CmpC(i));
    }
    pub fn cmp_erase(&mut self,u:&[QubitId],k:u64,target:QubitId,temps:&[QubitId]) {
        let i=self.cmp_spec(u,k,target,temps);self.g(G::CmpU(i));
    }
    fn cmp_prefix(&mut self,c:&CmpCall,stop:usize)->(Vec<G>,Option<QubitId>) {
        let add=(1u64<<c.u.len())-c.k;
        self.begin();let mut carry=None;let mut used=0;
        for i in 0..stop {
            let one=add>>i&1!=0;
            match (one,carry) {
                (true,None)=>carry=Some(c.u[i]),
                (false,None)=>{},
                (false,Some(q))=>{
                    self.and_c(c.u[i],q,c.temps[used]);carry=Some(c.temps[used]);used+=1;
                },
                (true,Some(q))=>{
                    self.x(c.u[i]);self.x(q);self.and_c(c.u[i],q,c.temps[used]);
                    self.x(q);self.x(c.u[i]);self.x(c.temps[used]);
                    carry=Some(c.temps[used]);used+=1;
                },
            }
        }
        (self.end(),carry)
    }
    fn cmp_call(&mut self,c:&CmpCall,compute:bool) {
        let n=c.u.len();
        if compute || !cmp_mbu_enabled() {
            let(r,carry)=self.cmp_prefix(c,n);self.play(&r,false);
            if let Some(q)=carry {self.cx(q,c.target);}self.x(c.target);
            self.play(&r,true);return;
        }
        // target=1 xor carry_n. Snapshot its X outcome before prefix
        // measurements reuse the scratch classical bit.
        let m=self.bit;
        self.raw(Op{kind:OperationType::Hmr,q_target:c.target,c_target:m,..Op::empty()});
        self.raw(Op{kind:OperationType::PushCondition,c_condition:m,..Op::empty()});
        let(r,carry)=self.cmp_prefix(c,n-1);self.play(&r,false);
        let last=c.u[n-1];let one=((1u64<<n)-c.k)>>(n-1)&1!=0;
        self.raw(Op{kind:OperationType::Neg,..Op::empty()});
        match carry {
            None=>{if one {self.raw(Op{kind:OperationType::Z,q_target:last,..Op::empty()});}},
            Some(q)=>{
                self.cz(last,q);
                if one {
                    self.raw(Op{kind:OperationType::Z,q_target:last,..Op::empty()});
                    self.raw(Op{kind:OperationType::Z,q_target:q,..Op::empty()});
                }
            },
        }
        self.play(&r,true);
        self.raw(Op{kind:OperationType::PopCondition,..Op::empty()});
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
    pub(crate) fn circuit_chart(&mut self,compute:Vec<G>,phase:Vec<G>,target:QubitId,cond:BitId,mode:u8){
        let id=self.circuit_charts.len();self.circuit_charts.push(CircuitChart{compute,phase,target,cond});
        self.g(match mode{0=>G::CircuitC(id),1=>G::CircuitU(id),_=>G::CircuitP(id)});
    }
    /// Lane cloud-lily852: register an ANF chart call (see G::AnfC / AnfU / AnfP).
    pub(crate) fn anf_spec(&mut self, mut call: AnfCall) -> usize {
        self.anf_calls.push(call);
        self.anf_calls.len() - 1
    }
    /// mode 0: target ^= f (target |0> before); 1: target (= f) -> |0> by X measurement and (-1)^f under the outcome;
    /// 2: (-1)^f under `cond`.
    fn anf_call(&mut self, c: &AnfCall, mode: u8) {
        if mode == 1 {
            let m = self.bit;
            self.raw(Op { kind: OperationType::Hmr, q_target: c.target, c_target: m, ..Op::empty() });
            self.raw(Op { kind: OperationType::PushCondition, c_condition: m, ..Op::empty() });
        } else if mode == 2 {
            self.raw(Op { kind: OperationType::PushCondition, c_condition: c.cond, ..Op::empty() });
        }
        if let Some((&r0, rest)) = c.fold.split_first() {
            for &r in rest { self.cx(r, r0); }
            if c.flip { self.x(r0); }
        }
        let mut clean=c.clean.clone();
        if mode==1 && !clean.contains(&c.target){clean.push(c.target);}
        let mut best=vec![];let mut best_cost=f64::INFINITY;
        for style in [0,if mode==0{1}else{2},if mode==0{3}else{4}]{
            let (terms,affine)=super::affine_anf::optimize_style(&c.terms,style);
            self.begin();
            for &(a,c,t) in &affine{if a==t{self.x(t)}else if c==t{self.cx(a,t)}else{self.ccx(a,c,t)}}
            self.anf_terms_clean(&terms,if mode==0{Some(c.target)}else{None},&clean,&c.dirty);
            for &(a,c,t) in affine.iter().rev(){if a==t{self.x(t)}else if c==t{self.cx(a,t)}else{self.ccx(a,c,t)}}
            let rec=self.end();let cost=self.measure(&rec,false);
            if cost<best_cost{best_cost=cost;best=rec;}
        }
        self.play(&best,false);
        if let Some((&r0, rest)) = c.fold.split_first() {
            if c.flip { self.x(r0); }
            for &r in rest.iter().rev() { self.cx(r, r0); }
        }
        if mode != 0 {
            self.raw(Op { kind: OperationType::PopCondition, ..Op::empty() });
        }
    }
    /// (-1)^AND(k): Z / CZ / CCZ, else the dirty V-chain of mcx_dirty with CCZ in place of its two target toggles.
    /// Factor shared products through restored dirty loans. Two identical target/phase applications
    /// cancel the borrowed value, leaving precisely the desired product polynomial.
    pub(crate) fn anf_terms_clean(&mut self,terms:&[Vec<QubitId>],target:Option<QubitId>,clean:&[QubitId],dirty:&[QubitId]){
        let vars:std::collections::BTreeSet<_>=terms.iter().flatten().map(|q|q.0).collect();
        let loan=clean.iter().copied().find(|q|Some(*q)!=target&&!vars.contains(&q.0));
        let Some(loan)=loan else{return self.anf_terms_clean_base(terms,target,clean,dirty)};
        let mut cofactors:std::collections::BTreeMap<(u64,u64),Vec<Vec<u64>>>=std::collections::BTreeMap::new();
        for t in terms {for i in 0..t.len(){for j in i+1..t.len(){
            let a=t[i].0.min(t[j].0);let c=t[i].0.max(t[j].0);
            let mut rest:Vec<_>=t.iter().map(|q|q.0).filter(|q|*q!=a&&*q!=c).collect();rest.sort();
            cofactors.entry((a,c)).or_default().push(rest);
        }}}
        let mut groups:std::collections::BTreeMap<Vec<Vec<u64>>,Vec<(u64,u64)>>=std::collections::BTreeMap::new();
        for(pair,mut cofactor)in cofactors{cofactor.sort();groups.entry(cofactor).or_default().push(pair);}
        let weight=|n:usize|{let n=if target.is_none(){n.saturating_sub(1)}else{n};match n{0|1=>0isize,2=>1,_=>(4*n-8)as isize}};
        let mut best=None;let mut best_gain=0;
        for(cofactor,pairs)in groups{if pairs.len()<2{continue;}
            let old:isize=cofactor.iter().map(|t|weight(t.len()+2)).sum::<isize>()*pairs.len()as isize;
            let new=pairs.len()as isize+cofactor.iter().map(|t|weight(t.len()+1)).sum::<isize>();
            if old-new>best_gain{best_gain=old-new;best=Some((cofactor,pairs));}
        }
        let Some((cofactor,pairs))=best else{return self.anf_terms_clean_base(terms,target,clean,dirty)};
        let taken:std::collections::BTreeSet<Vec<u64>>=pairs.iter().flat_map(|&(a,c)|cofactor.iter().map(move|t|{assert!(!t.contains(&a)&&!t.contains(&c));let mut k=t.clone();k.extend([a,c]);k.sort();k})).collect();
        assert_eq!(taken.len(),pairs.len()*cofactor.len());
        let rest:Vec<_>=terms.iter().filter(|t|{let mut k:Vec<_>=t.iter().map(|q|q.0).collect();k.sort();!taken.contains(&k)}).cloned().collect();
        let group:Vec<_>=cofactor.iter().map(|t|{let mut k:Vec<_>=t.iter().copied().map(QubitId).collect();k.push(loan);k}).collect();
        let pairs:Vec<_>=pairs.into_iter().map(|(a,c)|(QubitId(a),QubitId(c))).collect();
        let cl:Vec<_>=clean.iter().copied().filter(|q|*q!=loan).collect();let dl:Vec<_>=dirty.iter().copied().filter(|q|*q!=loan).collect();
        self.begin();self.anf_terms_clean_base(terms,target,clean,dirty);let baseline=self.end();
        self.begin();self.quad_compute(loan,&[],&pairs);self.anf_terms_clean_base(&group,target,&cl,&dl);self.quad_erase(loan,&[],&pairs);self.anf_terms_clean(&rest,target,clean,dirty);let grouped=self.end();
        let cb=self.measure(&baseline,false);let cg=self.measure(&grouped,false);self.play(if cg<cb{&grouped}else{&baseline},false);
    }
    pub(crate) fn anf_terms_clean_base(&mut self,terms:&[Vec<QubitId>],target:Option<QubitId>,clean:&[QubitId],dirty:&[QubitId]){
        let vars:std::collections::BTreeSet<_>=terms.iter().flatten().copied().map(|q|q.0).collect();
        let loan=clean.iter().copied().find(|q|Some(*q)!=target&&!vars.contains(&q.0));
        if let Some(loan)=loan {
            let weight=|n:usize|{let n=if target.is_none(){n.saturating_sub(1)}else{n};match n{0|1=>0isize,2=>1,_=>(4*n-8)as isize}};
            let mut scores:std::collections::BTreeMap<(u64,u64),isize>=std::collections::BTreeMap::new();
            for t in terms {for i in 0..t.len(){for j in i+1..t.len(){
                *scores.entry((t[i].0.min(t[j].0),t[i].0.max(t[j].0))).or_insert(-1)+=weight(t.len())-weight(t.len()-1);
            }}}
            if let Some((&(a,c),&score))=scores.iter().max_by_key(|(pair,score)|(**score,std::cmp::Reverse(**pair))) {
                if score>0 {
                    let(a,c)=(QubitId(a),QubitId(c));let mut group=vec![];let mut rest=vec![];
                    for t in terms {if t.contains(&a)&&t.contains(&c){let mut t:Vec<_>=t.iter().copied().filter(|q|*q!=a&&*q!=c).collect();t.push(loan);group.push(t);}else{rest.push(t.clone());}}
                    let cl:Vec<_>=clean.iter().copied().filter(|q|*q!=loan).collect();let dl:Vec<_>=dirty.iter().copied().filter(|q|*q!=loan).collect();
                    self.and_c(a,c,loan);self.anf_terms_clean_base(&group,target,&cl,&dl);self.and_u(a,c,loan);
                    self.anf_terms_clean_base(&rest,target,clean,dirty);return;
                }
            }
        }
        self.anf_terms_emit(terms,target,dirty);
    }
    pub(crate) fn anf_terms_emit(&mut self, terms:&[Vec<QubitId>], target:Option<QubitId>, dirty:&[QubitId]) {
        fn mono_cost(n:usize,phase:bool)->isize {
            let n=if phase {n.saturating_sub(1)}else{n};
            match n {0|1=>0,2=>1,_=>(4*n-8) as isize}
        }
        let phase=target.is_none();
        let vars:std::collections::BTreeSet<u64>=terms.iter().flatten().map(|q|q.0).collect();
        let loan=dirty.iter().copied().find(|q|Some(*q)!=target && !vars.contains(&q.0));
        if let Some(loan)=loan {
            let mut scores:std::collections::BTreeMap<(u64,u64),isize>=std::collections::BTreeMap::new();
            for term in terms {
                let gain=mono_cost(term.len(),phase)-2*mono_cost(term.len().saturating_sub(1),phase);
                for i in 0..term.len(){for j in i+1..term.len(){
                    let a=term[i].0.min(term[j].0);let b=term[i].0.max(term[j].0);
                    *scores.entry((a,b)).or_insert(-2)+=gain;
                }}
            }
            if let Some((&(a,b),&score))=scores.iter().max_by_key(|(pair,score)|(**score,std::cmp::Reverse(**pair))) {
                if score>0 {
                    let(a,b)=(QubitId(a),QubitId(b));let mut group=vec![];let mut rest=vec![];
                    for term in terms {
                        if term.contains(&a)&&term.contains(&b){
                            let mut k:Vec<_>=term.iter().copied().filter(|q|*q!=a&&*q!=b).collect();k.push(loan);group.push(k);
                        }else{rest.push(term.clone());}
                    }
                    let dl:Vec<_>=dirty.iter().copied().filter(|q|*q!=loan).collect();
                    self.ccx(a,b,loan);self.anf_terms_emit(&group,target,&dl);
                    self.ccx(a,b,loan);self.anf_terms_emit(&group,target,&dl);
                    self.anf_terms_emit(&rest,target,dirty);return;
                }
            }
        }
        for k in terms {
            let dl:Vec<_>=dirty.iter().copied().filter(|d|Some(*d)!=target&&!k.contains(d)).collect();
            if let Some(t)=target {
                if k.is_empty(){self.x(t);}else{let lits:Vec<_>=k.iter().map(|&q|(q,false)).collect();super::mask::mc_xor(self,&lits,t,&[],&dl);}
            }else{self.anf_phase_mono(k,&dl);}
        }
    }
    fn anf_phase_mono(&mut self, k: &[QubitId], dirty: &[QubitId]) {
        let ccz = |b: &mut B, a: QubitId, c: QubitId, t: QubitId| {
            b.g(G::Ccz(a,c,t));
        };
        match k.len() {
            0 => self.g(G::Neg),
            1 => self.z_if(k[0],NO_BIT),
            2 => self.cz(k[0], k[1]),
            n => {
                let (ctrl, t) = (&k[..n - 1], k[n - 1]);
                let kc = ctrl.len();
                if kc == 2 { ccz(self, ctrl[0], ctrl[1], t); return; }
                assert!(dirty.len() >= kc - 2, "not enough dirty ancillas");
                let a = &dirty[..kc - 2];
                for _ in 0..2 {
                    ccz(self, ctrl[kc - 1], a[kc - 3], t);
                    for i in (1..kc - 2).rev() { self.ccx(ctrl[i + 1], a[i - 1], a[i]); }
                    self.ccx(ctrl[0], ctrl[1], a[0]);
                    for i in 1..kc - 2 { self.ccx(ctrl[i + 1], a[i - 1], a[i]); }
                }
            }
        }
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

    /// retake799 (825-down): the phase path of carry_call with p < n - 1 pool lanes (ctl = ONE): a bridged chain.
    fn carry_call_bridged(&mut self, spec: &CarryCall, phase: bool) {
        let (a, t, pool) = (&spec.a, &spec.t, &spec.pool);
        let n = a.len();
        let p = pool.len();
        // with the constant control the top carry's phase is three CZ (lanes 0..n-2 carry); otherwise the top carry
        // c_n itself is needed on a lane (lanes 0..n-1 carry) for cz(ctl, c_n) or ccx(ctl, c_n, flag)
        let top_cz = phase && spec.ctl == ONE;
        let last = if top_cz { n - 1 } else { n };
        assert!(n >= 3 && p < last && 2 * p >= last + 1, "bridged carry: pool {p} for {n} lanes");
        // the carry-out of lane i is cw(i); the bridge is the carry-out of lane k - 1
        let k = last + 1 - p;
        let mut l2: Vec<QubitId> = pool[..k - 1].to_vec();
        l2.extend_from_slice(&pool[k..]);
        assert!(l2.len() >= last - k);
        let cw = |i: usize| -> QubitId { if i < k { pool[i] } else { l2[i - k] } };
        let cin = |i: usize| -> Option<QubitId> { if i == 0 { spec.cin } else { Some(cw(i - 1)) } };
        let compute = |b: &mut Self, i: usize| match cin(i) {
            None => b.and_c(a[0], t[0], cw(0)),
            Some(ci) => {
                b.cx(ci, a[i]);
                b.cx(ci, t[i]);
                b.and_c(a[i], t[i], cw(i));
                b.cx(ci, cw(i));
            }
        };
        let uncompute = |b: &mut Self, i: usize| match cin(i) {
            None => b.and_u(a[0], t[0], cw(0)),
            Some(ci) => {
                b.cx(ci, cw(i));
                b.and_u(a[i], t[i], cw(i));
                b.cx(ci, t[i]);
                b.cx(ci, a[i]);
            }
        };
        // segment 1: lanes 0..k-1, then the lower carries away (lane k-1's carry, the bridge, stays)
        for i in 0..k { compute(self, i); }
        for i in (0..k - 1).rev() { uncompute(self, i); }
        // segment 2 from the bridge: lanes k..last-1
        for i in k..last { compute(self, i); }
        if top_cz {
            // the top lane's carry phase (MAJ's quadratic polynomial)
            self.cz(a[n - 1], t[n - 1]);
            let c = cw(n - 2);
            self.cz(a[n - 1], c);
            self.cz(t[n - 1], c);
        } else if phase {
            self.cz(spec.ctl, cw(n - 1));
        } else {
            self.ccx(spec.ctl, cw(n - 1), spec.flag);
        }
        for i in (k..last).rev() { uncompute(self, i); }
        // segment 1's lower carries back, then the whole chain away in order
        for i in 0..k - 1 { compute(self, i); }
        for i in (0..k).rev() { uncompute(self, i); }
    }

    fn carry_call(&mut self, spec: &CarryCall, phase: bool) {
        let (a, t, pool) = (&spec.a, &spec.t, &spec.pool);
        let n = a.len();
        if pool.len() < (if phase && spec.ctl == ONE { n - 1 } else { n }) {
            return self.carry_call_bridged(spec, phase);
        }
        let cin = |i: usize| if i == 0 { spec.cin } else { Some(pool[i - 1]) };
        // Unconditional carry phase = MAJ's quadratic polynomial on the top lane.
        // Lower carries are restored by the same measurement uncomputes.
        let last_phase = phase && spec.ctl == ONE;
        // retake799: a short pool (n - 1 lanes, ctl = ONE): the compute writes MAJ of the top lane straight into flag
        let short = pool.len() < n;
        assert!(!short || spec.ctl == ONE);
        // only the erase (phase) path takes a short pool here; it is the existing last_phase path
        assert!(!short || phase, "retake799: short-pool carry compute is not used at these caps");
        let last_compute = !phase && short;
        let m = if last_phase || last_compute { n - 1 } else { n };
        for i in 0..m {
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
        if last_phase {
            self.cz(a[n-1],t[n-1]);
            if let Some(c) = cin(n-1) {
                self.cz(a[n-1],c);
                self.cz(t[n-1],c);
            }
        } else if last_compute {
            match cin(n - 1) {
                None => self.ccx(a[n - 1], t[n - 1], spec.flag),
                Some(c) => {
                    self.cx(c, a[n - 1]);
                    self.cx(c, t[n - 1]);
                    self.ccx(a[n - 1], t[n - 1], spec.flag);
                    self.cx(c, spec.flag);
                    self.cx(c, t[n - 1]);
                    self.cx(c, a[n - 1]);
                }
            }
        } else if phase {
            self.cz(spec.ctl, pool[n - 1]);
        } else {
            self.ccx(spec.ctl, pool[n - 1], spec.flag);
        }
        for i in (0..m).rev() {
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
    /// Classical operand bit controlling a Clifford; outside recordings only.
    pub fn cx_if(&mut self,c:QubitId,t:QubitId,bit:BitId) {
        assert!(self.rec.is_empty());
        self.raw(Op {kind:OperationType::CX,q_control1:c,q_target:t,c_condition:bit,..Op::empty()});
    }
    pub fn cx(&mut self, c: QubitId, t: QubitId) {
        if c == ONE {
            return self.x(t);
        }
        self.g(G::Cx(c, t));
    }
    #[track_caller]
    pub fn ccx(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        if a == ONE {
            return self.cx(b, t);
        }
        if b == ONE {
            return self.cx(a, t);
        }
        assert!(a != t && b != t && a != b, "invalid CCX controls/target: {a:?} {b:?} {t:?}");
        self.g(G::Ccx(a, b, t));
    }
    pub fn cz(&mut self, a: QubitId, b: QubitId) {
        // O1 U20: CZ with the constant-|1> sentinel is a Z (emitted directly; never inside a recording).
        if a == ONE || b == ONE {
            assert!(self.rec.is_empty(), "Z with the ONE sentinel inside a recording");
            if a == ONE && b == ONE {
                return self.raw(Op { kind: OperationType::Neg, ..Op::empty() });
            }
            let q = if a == ONE { b } else { a };
            return self.raw(Op { kind: OperationType::Z, q_target: q, ..Op::empty() });
        }
        self.g(G::Cz(a, b));
    }
    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Swap(a, b));
    }
    /// t ^= a & b into a clean t. O1 U20: an operand equal to the ONE sentinel lowers the AND to a copy (0 T).
    pub fn and_c(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        match (a == ONE, b == ONE) {
            (true, true) => self.x(t),
            (true, false) => self.cx(b, t),
            (false, true) => self.cx(a, t),
            (false, false) => self.g(G::AndC(a, b, t)),
        }
    }
    /// Uncompute t = a & b. With a ONE operand t is a copy, cleared by the same copy.
    pub fn and_u(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        match (a == ONE, b == ONE) {
            (true, true) => self.x(t),
            (true, false) => self.cx(b, t),
            (false, true) => self.cx(a, t),
            (false, false) => self.g(G::AndU(a, b, t)),
        }
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
        self.native_square_at_cap(out,y,975);
    }
    pub fn native_square_at_cap(&mut self, out: &[QubitId], y: &[QubitId], cap: u64) {
        assert!(self.rec.is_empty() && self.cond_depth == 0);
        assert_eq!(out.len(), 256); assert_eq!(y.len(), 256);
        assert_eq!(self.live, 512, "native square requires exactly two live coordinates");
        let ops = super::super::public_square_port::native_square_ops_at_cap(cap as usize);
        let (nq, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
        assert!(nq <= cap && nq >= 512, "closed native square touched {nq} exceeds explicit cap {cap}");
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
        assert_eq!(self.live,512,"closed native square must return exactly its two coordinates");
    }
    pub fn native_flat_square_at_cap(&mut self, out: &[QubitId], y: &[QubitId], cap: u64) {
        assert!(self.rec.is_empty() && self.cond_depth == 0);
        assert_eq!(out.len(), 256); assert_eq!(y.len(), 256);
        assert_eq!(self.live, 512, "native flat square requires exactly two live coordinates");
        let ops = super::super::public_square_port::native_flat_square_ops_at_cap(cap as usize);
        let (nq, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
        assert!(nq <= cap && nq >= 512, "closed native flat square touched {nq} exceeds explicit cap {cap}");
        let scratch = self.alloc_n(nq as usize - 512);
        let mut qm = out.to_vec(); qm.extend_from_slice(y); qm.extend_from_slice(&scratch);
        let cm = self.fresh_bits(nb as usize);
        for mut op in ops {
            assert_eq!(op.r_target, NO_REG, "flat square block must have no register declarations");
            for q in [&mut op.q_target, &mut op.q_control1, &mut op.q_control2] {
                if *q != NO_QUBIT { *q = qm[q.0 as usize]; }
            }
            for c in [&mut op.c_target, &mut op.c_condition] {
                if *c != NO_BIT { *c = cm[c.0 as usize]; }
            }
            if matches!(op.kind, OperationType::CCX | OperationType::CCZ) {
                self.tof += 1;
                assert_eq!(op.c_condition, NO_BIT);
            }
            self.raw(op);
        }
        self.free_n(&scratch);
        assert_eq!(self.live, 512, "closed native flat square must return its two coordinates");
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
    // ---------------------------------------------------------------- classical bit arithmetic (0 Toffoli)
    /// t ^= AND(conds) on classical bits (no conds: t ^= 1), with singly conditioned bit ops only (no condition stack,
    /// so every PushCondition in the stream still follows its measurement): an AND of two bits is formed in a fresh bit
    /// as copy(b), then cleared under ~a. Outside recordings only; emits no quantum gate.
    pub fn cbit_xor_and(&mut self, t: BitId, conds: &[BitId]) {
        assert!(self.rec.is_empty(), "classical bit op inside a recording");
        assert!(!conds.contains(&t));
        let mut acc = NO_BIT;
        for &c in conds {
            acc = if acc == NO_BIT { c } else { self.cbit_and(acc, c) };
        }
        self.raw(Op { kind: OperationType::BitInvert, c_target: t, c_condition: acc, ..Op::empty() });
    }
    /// A fresh classical bit holding a & b (singly conditioned ops).
    fn cbit_and(&mut self, a: BitId, b: BitId) -> BitId {
        let fr = self.fresh_bits(2);
        let (t, na) = (fr[0], fr[1]);
        self.raw(Op { kind: OperationType::BitInvert, c_target: t, c_condition: b, ..Op::empty() });
        self.raw(Op { kind: OperationType::BitInvert, c_target: na, ..Op::empty() });
        self.raw(Op { kind: OperationType::BitInvert, c_target: na, c_condition: a, ..Op::empty() });
        self.raw(Op { kind: OperationType::BitStore0, c_target: t, c_condition: na, ..Op::empty() });
        t
    }
    /// Classical ripple add a += b + cin mod 2^|a| (b zero-extended; CSrc per lane), every update of `a` under `when` if
    /// given (carries are formed unconditionally and gated where they act). Carries live in fresh bits; returns the
    /// carry out (gated by `when`).
    pub fn c_add(&mut self, a: &[BitId], b: &[CSrc], cin: bool, when: Option<BitId>) -> BitId {
        assert!(self.rec.is_empty() && b.len() <= a.len());
        let mut c = self.fresh_bits(1)[0];
        if cin {
            self.cbit_xor_and(c, &[]);
        }
        let gate: Vec<BitId> = when.into_iter().collect();
        for (i, &ai) in a.iter().enumerate() {
            let bi = b.get(i).copied().unwrap_or(CSrc::Zero);
            let co = self.fresh_bits(1)[0];
            // co = MAJ(ai, bi, c), from the pre-update ai
            match bi {
                CSrc::Zero => self.cbit_xor_and(co, &[ai, c]),
                CSrc::One => {
                    self.cbit_xor_and(co, &[ai]);
                    self.cbit_xor_and(co, &[c]);
                    self.cbit_xor_and(co, &[ai, c]);
                }
                CSrc::Bit(bb) => {
                    self.cbit_xor_and(co, &[ai, bb]);
                    self.cbit_xor_and(co, &[ai, c]);
                    self.cbit_xor_and(co, &[bb, c]);
                }
            }
            // ai ^= when & (bi ^ c)
            let with = |s: &mut Self, extra: &[BitId]| {
                let mut v = gate.clone();
                v.extend_from_slice(extra);
                s.cbit_xor_and(ai, &v);
            };
            match bi {
                CSrc::Zero => {}
                CSrc::One => with(self, &[]),
                CSrc::Bit(bb) => with(self, &[bb]),
            }
            with(self, &[c]);
            c = co;
        }
        match when {
            Some(w) => {
                let g = self.fresh_bits(1)[0];
                self.cbit_xor_and(g, &[w, c]);
                g
            }
            None => c,
        }
    }
    /// Classical a <- a - k if a >= k else a (k a constant given LSB first as bools, |k| <= |a|), mod 2^|a|.
    pub fn c_cond_sub_const(&mut self, a: &[BitId], k: &[bool]) {
        let w = a.len();
        assert!(k.len() <= w);
        let kb = |i: usize| i < k.len() && k[i];
        // a + ~k + 1: carry out = [a >= k]
        let nk: Vec<CSrc> = (0..w).map(|i| if kb(i) { CSrc::Zero } else { CSrc::One }).collect();
        let ge = self.c_add(a, &nk, true, None);
        let lt = self.fresh_bits(1)[0];
        self.cbit_xor_and(lt, &[]);
        self.cbit_xor_and(lt, &[ge]);
        let kk: Vec<CSrc> = (0..w).map(|i| if kb(i) { CSrc::One } else { CSrc::Zero }).collect();
        self.c_add(a, &kk, false, Some(lt));
    }

    /// Controlled swap (Fredkin), 1 Toffoli.
    pub fn cswap(&mut self, c: QubitId, a: QubitId, b: QubitId) {
        self.cx(b, a);
        self.ccx(c, a, b);
        self.cx(b, a);
    }
}
