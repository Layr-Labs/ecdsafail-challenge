//! Exact bounded one- and two-holder current-slot product witnesses.
//!
//! Values are square-free ANFs of degree at most three and at most 64
//! monomials over immutable atoms.  Unsupported state updates become a fresh
//! atom for the complete value.  Queries never create atoms: they either
//! prove an exact product or decline the rewrite.

use crate::circuit::{analyze_ops, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT, NO_QUBIT};
use std::collections::{BTreeSet, HashMap};

const DEGREE_CAP: usize = 3;
const MONOMIAL_CAP: usize = 64;

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
struct Mono {
    len: u8,
    ids: [u64; DEGREE_CAP],
}

impl Mono {
    fn one() -> Self { Self { len: 0, ids: [0; DEGREE_CAP] } }
    fn atom(id: u64) -> Self {
        let mut ids = [0; DEGREE_CAP];
        ids[0] = id;
        Self { len: 1, ids }
    }
    fn mul(&self, other: &Self) -> Option<Self> {
        let mut merged = [0u64; 2 * DEGREE_CAP];
        let mut n = 0;
        for &id in &self.ids[..self.len as usize] { merged[n] = id; n += 1; }
        for &id in &other.ids[..other.len as usize] { merged[n] = id; n += 1; }
        merged[..n].sort_unstable();
        let mut ids = [0; DEGREE_CAP];
        let mut len = 0;
        for i in 0..n {
            if i != 0 && merged[i] == merged[i - 1] { continue; }
            if len == DEGREE_CAP { return None; }
            ids[len] = merged[i];
            len += 1;
        }
        Some(Self { len: len as u8, ids })
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct Expr { terms: Vec<Mono> }

impl Expr {
    fn zero() -> Self { Self { terms: vec![] } }
    fn one() -> Self { Self { terms: vec![Mono::one()] } }
    fn atom(id: u64) -> Self { Self { terms: vec![Mono::atom(id)] } }
    fn is_zero(&self) -> bool { self.terms.is_empty() }
    fn is_one(&self) -> bool { self.terms.len() == 1 && self.terms[0].len == 0 }
    fn complement(&self) -> Self {
        let mut terms = self.terms.iter().cloned().collect::<BTreeSet<_>>();
        let one = Mono::one();
        if !terms.insert(one.clone()) { terms.remove(&one); }
        Self { terms: terms.into_iter().collect() }
    }
    fn complements(&self, other: &Self) -> bool { self.complement() == *other }
    fn degree(&self) -> usize { self.terms.iter().map(|m| m.len as usize).max().unwrap_or(0) }
}

struct Engine { next_atom: u64, abstractions: u64 }

impl Engine {
    fn fresh(&mut self) -> Expr {
        let id = self.next_atom;
        self.next_atom = self.next_atom.checked_add(1).expect("atom id overflow");
        self.abstractions += 1;
        Expr::atom(id)
    }
    fn xor_exact(a: &Expr, b: &Expr) -> Option<Expr> {
        if a == b { return Some(Expr::zero()); }
        if a.is_zero() { return Some(b.clone()); }
        if b.is_zero() { return Some(a.clone()); }
        if a.is_one() { return Some(b.complement()); }
        if b.is_one() { return Some(a.complement()); }
        let mut terms = a.terms.iter().cloned().collect::<BTreeSet<_>>();
        for term in &b.terms {
            if !terms.insert(term.clone()) { terms.remove(term); }
        }
        (terms.len() <= MONOMIAL_CAP).then(|| Expr { terms: terms.into_iter().collect() })
    }
    fn and_exact(a: &Expr, b: &Expr) -> Option<Expr> {
        if a.is_zero() || b.is_zero() || a.complements(b) { return Some(Expr::zero()); }
        if a.is_one() { return Some(b.clone()); }
        if b.is_one() || a == b { return Some(a.clone()); }
        let mut terms = BTreeSet::new();
        for left in &a.terms {
            for right in &b.terms {
                let product = left.mul(right)?;
                if !terms.insert(product.clone()) { terms.remove(&product); }
                if terms.len() > MONOMIAL_CAP { return None; }
            }
        }
        Some(Expr { terms: terms.into_iter().collect() })
    }
    fn xor(&mut self, a: &Expr, b: &Expr) -> Expr {
        Self::xor_exact(a, b).unwrap_or_else(|| self.fresh())
    }
    fn and(&mut self, a: &Expr, b: &Expr) -> Expr {
        Self::and_exact(a, b).unwrap_or_else(|| self.fresh())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rewrite {
    Keep,
    Drop,
    X,
    Cx(usize),
    ComplementedCx(usize),
    Z(usize),
    Cz(usize, usize),
    ComplementedCz { witness: usize, factor: usize },
    TwoCx { left: usize, right: usize, constant: bool },
    TwoCz { left: usize, right: usize, factor: usize, constant: bool },
}

impl Rewrite {
    fn gate(mut original: Op, kind: K, q1: Option<usize>, target: Option<usize>, out: &mut Vec<Op>) {
        original.kind = kind;
        original.q_control2 = NO_QUBIT;
        original.q_control1 = q1.map(|q| QubitId(q as u64)).unwrap_or(NO_QUBIT);
        original.q_target = target.map(|q| QubitId(q as u64)).unwrap_or(NO_QUBIT);
        original.validate();
        out.push(original);
    }
    fn emit(self, original: Op, out: &mut Vec<Op>) {
        let target = original.q_target.0 as usize;
        match self {
            Self::Keep => out.push(original),
            Self::Drop => {},
            Self::X => Self::gate(original, K::X, None, Some(target), out),
            Self::Cx(witness) => Self::gate(original, K::CX, Some(witness), Some(target), out),
            Self::ComplementedCx(witness) => {
                Self::gate(original, K::X, None, Some(target), out);
                Self::gate(original, K::CX, Some(witness), Some(target), out);
            }
            Self::Z(witness) => Self::gate(original, K::Z, None, Some(witness), out),
            Self::Cz(witness, factor) => {
                if witness == factor { Self::gate(original, K::Z, None, Some(factor), out); }
                else { Self::gate(original, K::CZ, Some(witness), Some(factor), out); }
            }
            Self::ComplementedCz { witness, factor } => {
                // (~w)*f = f XOR w*f.  The witness and factor retain their
                // original values throughout this diagonal replacement.
                Self::gate(original, K::Z, None, Some(factor), out);
                if witness == factor {
                    Self::gate(original, K::Z, None, Some(factor), out);
                } else {
                    Self::gate(original, K::CZ, Some(witness), Some(factor), out);
                }
            }
            Self::TwoCx { left, right, constant } => {
                if constant { Self::gate(original, K::X, None, Some(target), out); }
                Self::gate(original, K::CX, Some(left), Some(target), out);
                Self::gate(original, K::CX, Some(right), Some(target), out);
            }
            Self::TwoCz { left, right, factor, constant } => {
                if constant { Self::gate(original, K::Z, None, Some(factor), out); }
                for witness in [left, right] {
                    if witness == factor { Self::gate(original, K::Z, None, Some(factor), out); }
                    else { Self::gate(original, K::CZ, Some(witness), Some(factor), out); }
                }
            }
        }
    }
    fn name(self) -> &'static str {
        match self {
            Self::Keep => "keep", Self::Drop => "drop", Self::X => "x",
            Self::Cx(_) => "cx", Self::ComplementedCx(_) => "x_cx",
            Self::Z(_) => "z", Self::Cz(_, _) => "cz",
            Self::ComplementedCz { .. } => "z_cz",
            Self::TwoCx { constant: false, .. } => "cx_cx",
            Self::TwoCx { constant: true, .. } => "x_cx_cx",
            Self::TwoCz { constant: false, .. } => "cz_cz",
            Self::TwoCz { constant: true, .. } => "z_cz_cz",
        }
    }
}

#[derive(Default, Clone, Debug)]
pub(crate) struct Stats {
    pub input_ops: usize,
    pub output_ops: usize,
    pub ccx_rewrites: u64,
    pub ccz_rewrites: u64,
    pub exact_holder_hits: u64,
    pub complement_holder_hits: u64,
    pub direct_hits: u64,
    pub two_holder_hits: u64,
    pub two_holder_complement_hits: u64,
    pub native_saved: u64,
    pub expected_saved: f64,
    pub abstractions: u64,
    pub first_hits: Vec<String>,
}

struct State {
    engine: Engine,
    qubits: Vec<Expr>,
    bits: Vec<Expr>,
    base_condition: Expr,
    condition_stack: Vec<Expr>,
    index: HashMap<Expr, BTreeSet<usize>>,
    term_index: HashMap<Mono, BTreeSet<usize>>,
    eligible: Vec<bool>,
    depth: i32,
}

fn quantum_changes(op: &Op) -> Vec<usize> {
    match op.kind {
        K::X | K::CX | K::CCX | K::R | K::Hmr => vec![op.q_target.0 as usize],
        K::Swap => vec![op.q_control1.0 as usize, op.q_target.0 as usize],
        _ => vec![],
    }
}

fn quantum_touches(op: &Op) -> Vec<usize> {
    match op.kind {
        K::X | K::Z | K::R | K::Hmr => vec![op.q_target.0 as usize],
        K::CX | K::CZ | K::Swap => vec![op.q_control1.0 as usize, op.q_target.0 as usize],
        K::CCX | K::CCZ => vec![op.q_control1.0 as usize, op.q_control2.0 as usize, op.q_target.0 as usize],
        _ => vec![],
    }
}

impl State {
    fn new(ops: &[Op]) -> Self {
        let (nq, nb, _, registers) = analyze_ops(ops.iter());
        let mut q_inputs = vec![false; nq as usize];
        let mut b_inputs = vec![false; nb as usize];
        for register in registers {
            for slot in register {
                match slot {
                    QubitOrBit::Qubit(q) => q_inputs[q.0 as usize] = true,
                    QubitOrBit::Bit(b) => b_inputs[b.0 as usize] = true,
                }
            }
        }
        let mut engine = Engine { next_atom: 0, abstractions: 0 };
        let mut qubits = vec![Expr::zero(); nq as usize];
        let mut bits = vec![Expr::zero(); nb as usize];
        for (q, input) in q_inputs.iter().enumerate() { if *input { qubits[q] = engine.fresh(); } }
        for (b, input) in b_inputs.iter().enumerate() { if *input { bits[b] = engine.fresh(); } }
        let eligible = q_inputs;
        let mut state = Self {
            engine, qubits, bits, base_condition: Expr::one(), condition_stack: vec![],
            index: HashMap::new(), term_index: HashMap::new(), eligible, depth: 0,
        };
        for q in 0..state.qubits.len() { state.insert(q); }
        state
    }
    fn insert(&mut self, q: usize) {
        if self.eligible[q] {
            self.index.entry(self.qubits[q].clone()).or_default().insert(q);
            for term in &self.qubits[q].terms { self.term_index.entry(term.clone()).or_default().insert(q); }
        }
    }
    fn remove(&mut self, q: usize) {
        if !self.eligible[q] { return; }
        let value = &self.qubits[q];
        if let Some(slots) = self.index.get_mut(value) {
            assert!(slots.remove(&q));
            if slots.is_empty() { self.index.remove(value); }
        }
        for term in &value.terms {
            if let Some(slots) = self.term_index.get_mut(term) {
                assert!(slots.remove(&q));
                if slots.is_empty() { self.term_index.remove(term); }
            }
        }
    }
    fn lookup(&self, value: &Expr, excluded: &[usize], allow_complement: bool) -> Option<(usize, bool)> {
        for (candidate, complemented) in [(value.clone(), false), (value.complement(), true)] {
            if complemented && !allow_complement { continue; }
            if let Some(slots) = self.index.get(&candidate) {
                if let Some(&q) = slots.iter().find(|q| !excluded.contains(q)) { return Some((q, complemented)); }
            }
        }
        None
    }
    /// Find value = holder1 XOR holder2 [XOR 1] without scanning all pairs.
    /// If d=holder1 XOR holder2, every monomial of d occurs in exactly one
    /// holder. Pick d's rarest indexed monomial, then hash-lookup the partner.
    fn lookup_pair(&self, value: &Expr, excluded: &[usize], allow_complement: bool) -> Option<(usize, usize, bool)> {
        for (difference, constant) in [(value.clone(), false), (value.complement(), true)] {
            if constant && !allow_complement { continue; }
            let Some(rare) = difference.terms.iter().min_by_key(|term| self.term_index.get(*term).map_or(usize::MAX, BTreeSet::len)) else { continue; };
            let Some(candidates) = self.term_index.get(rare) else { continue; };
            for &left in candidates {
                if excluded.contains(&left) { continue; }
                let Some(right_value) = Engine::xor_exact(&self.qubits[left], &difference) else { continue; };
                let Some(slots) = self.index.get(&right_value) else { continue; };
                if let Some(&right) = slots.iter().find(|&&q| q != left && !excluded.contains(&q)) {
                    return Some((left, right, constant));
                }
            }
        }
        None
    }
    fn direct_ccx(a: &Expr, b: &Expr, op: &Op) -> Rewrite {
        if a.is_zero() || b.is_zero() || a.complements(b) { Rewrite::Drop }
        else if a.is_one() && b.is_one() { Rewrite::X }
        else if a.is_one() { Rewrite::Cx(op.q_control2.0 as usize) }
        else if b.is_one() || a == b { Rewrite::Cx(op.q_control1.0 as usize) }
        else { Rewrite::Keep }
    }
    fn query(&self, op: &Op) -> (Rewrite, bool, bool) {
        if !matches!(op.kind, K::CCX | K::CCZ) { return (Rewrite::Keep, false, false); }
        let qa = op.q_control1.0 as usize;
        let qb = op.q_control2.0 as usize;
        let qt = op.q_target.0 as usize;
        let a = &self.qubits[qa];
        let b = &self.qubits[qb];
        if op.kind == K::CCX {
            let direct = Self::direct_ccx(a, b, op);
            if direct != Rewrite::Keep { return (direct, false, true); }
            let Some(product) = Engine::and_exact(a, b) else { return (Rewrite::Keep, false, false); };
            if let Some((witness, complemented)) = self.lookup(&product, &[qt], true) {
                return (if complemented { Rewrite::ComplementedCx(witness) } else { Rewrite::Cx(witness) }, complemented, false);
            }
            if let Some((left, right, constant)) = self.lookup_pair(&product, &[qt], true) {
                return (Rewrite::TwoCx { left, right, constant }, constant, false);
            }
            return (Rewrite::Keep, false, false);
        }

        // A zero triple has no phase.  An exact current holder of the full
        // triple gives a single Z.  Otherwise try every pair orientation and
        // retain the third factor for CZ.
        if let Some(ab) = Engine::and_exact(a, b) {
            if let Some(phase) = Engine::and_exact(&ab, &self.qubits[qt]) {
                if phase.is_zero() { return (Rewrite::Drop, false, true); }
                if let Some((witness, _)) = self.lookup(&phase, &[], false) {
                    return (Rewrite::Z(witness), false, false);
                }
            }
        }
        for (left, right, factor) in [(qa, qb, qt), (qa, qt, qb), (qb, qt, qa)] {
            let Some(pair) = Engine::and_exact(&self.qubits[left], &self.qubits[right]) else { continue; };
            if pair.is_zero() { return (Rewrite::Drop, false, true); }
            if pair.is_one() { return (Rewrite::Z(factor), false, true); }
            if let Some((witness, complemented)) = self.lookup(&pair, &[], true) {
                if complemented && witness == factor {
                    // pair = ~factor, hence pair*factor = 0.
                    return (Rewrite::Drop, true, false);
                }
                return (
                    if complemented { Rewrite::ComplementedCz { witness, factor } }
                    else { Rewrite::Cz(witness, factor) },
                    complemented,
                    false,
                );
            }
            if let Some((left_holder, right_holder, constant)) = self.lookup_pair(&pair, &[], true) {
                return (Rewrite::TwoCz { left: left_holder, right: right_holder, factor, constant }, constant, false);
            }
        }
        (Rewrite::Keep, false, false)
    }
    fn step(&mut self, op: &Op) {
        if op.kind == K::PushCondition {
            self.condition_stack.push(self.base_condition.clone());
            let bit = self.bits[op.c_condition.0 as usize].clone();
            self.base_condition = self.engine.and(&self.base_condition.clone(), &bit);
            self.depth += 1;
            return;
        }
        if op.kind == K::PopCondition {
            self.base_condition = self.condition_stack.pop().expect("balanced condition stack");
            self.depth -= 1;
            return;
        }
        let condition = if op.c_condition == NO_BIT { self.base_condition.clone() }
            else { self.engine.and(&self.base_condition.clone(), &self.bits[op.c_condition.0 as usize].clone()) };
        match op.kind {
            K::CCX => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let b = self.qubits[op.q_control2.0 as usize].clone();
                let product = self.engine.and(&a, &b);
                let toggle = self.engine.and(&condition, &product);
                let t = op.q_target.0 as usize;
                self.qubits[t] = self.engine.xor(&self.qubits[t].clone(), &toggle);
            }
            K::CX => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let toggle = self.engine.and(&condition, &a);
                let t = op.q_target.0 as usize;
                self.qubits[t] = self.engine.xor(&self.qubits[t].clone(), &toggle);
            }
            K::X => {
                let t = op.q_target.0 as usize;
                self.qubits[t] = self.engine.xor(&self.qubits[t].clone(), &condition);
            }
            K::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                let left = self.qubits[a].clone();
                let right = self.qubits[b].clone();
                let difference = self.engine.xor(&left, &right);
                let toggle = self.engine.and(&condition, &difference);
                self.qubits[a] = self.engine.xor(&left, &toggle);
                self.qubits[b] = self.engine.xor(&right, &toggle);
            }
            K::Hmr => {
                let t = op.q_target.0 as usize;
                let bit = op.c_target.0 as usize;
                let outcome = self.engine.fresh();
                let old_bit = self.bits[bit].clone();
                let difference = self.engine.xor(&old_bit, &outcome);
                let toggle = self.engine.and(&condition, &difference);
                self.bits[bit] = self.engine.xor(&old_bit, &toggle);
                self.qubits[t] = self.engine.and(&self.qubits[t].clone(), &condition.complement());
            }
            K::R => {
                let t = op.q_target.0 as usize;
                self.qubits[t] = self.engine.and(&self.qubits[t].clone(), &condition.complement());
            }
            K::BitInvert => {
                let b = op.c_target.0 as usize;
                self.bits[b] = self.engine.xor(&self.bits[b].clone(), &condition);
            }
            K::BitStore0 => {
                let b = op.c_target.0 as usize;
                self.bits[b] = self.engine.and(&self.bits[b].clone(), &condition.complement());
            }
            K::BitStore1 => {
                let b = op.c_target.0 as usize;
                let missing = self.bits[b].complement();
                let set = self.engine.and(&condition, &missing);
                self.bits[b] = self.engine.xor(&self.bits[b].clone(), &set);
            }
            K::Neg | K::Register | K::AppendToRegister | K::Z | K::CZ | K::CCZ | K::DebugPrint => {},
            K::PushCondition | K::PopCondition => unreachable!(),
        }
    }
}

pub(crate) fn simplify(ops: Vec<Op>) -> (Vec<Op>, Stats) {
    let mut state = State::new(&ops);
    let mut out = Vec::with_capacity(ops.len());
    let mut stats = Stats { input_ops: ops.len(), ..Stats::default() };
    for (at, op) in ops.into_iter().enumerate() {
        for q in quantum_touches(&op) {
            if !state.eligible[q] { state.eligible[q] = true; state.insert(q); }
        }
        let (rewrite, complemented, direct) = state.query(&op);
        let changes = quantum_changes(&op);
        for &q in &changes { state.remove(q); }
        let weight = if matches!(op.kind, K::CCX | K::CCZ) {
            2f64.powi(-state.depth) * if op.c_condition == NO_BIT { 1.0 } else { 0.5 }
        } else { 0.0 };
        state.step(&op);
        if op.kind == K::R { state.eligible[op.q_target.0 as usize] = false; }
        for &q in &changes { state.insert(q); }
        if rewrite != Rewrite::Keep {
            stats.native_saved += 1;
            stats.expected_saved += weight;
            if op.kind == K::CCX { stats.ccx_rewrites += 1; } else { stats.ccz_rewrites += 1; }
            let two = matches!(rewrite, Rewrite::TwoCx { .. } | Rewrite::TwoCz { .. });
            if direct { stats.direct_hits += 1; }
            else if two {
                stats.two_holder_hits += 1;
                if complemented { stats.two_holder_complement_hits += 1; }
            }
            else if complemented { stats.complement_holder_hits += 1; }
            else { stats.exact_holder_hits += 1; }
            if stats.first_hits.len() < 96 {
                stats.first_hits.push(format!(
                    "{{\"op\":{at},\"kind\":\"{:?}\",\"rewrite\":\"{}\",\"q1\":{},\"q2\":{},\"target\":{},\"depth\":{},\"direct_condition\":{}}}",
                    op.kind, rewrite.name(), op.q_control1.0, op.q_control2.0, op.q_target.0,
                    state.depth, op.c_condition != NO_BIT,
                ));
            }
        }
        rewrite.emit(op, &mut out);
    }
    assert!(state.condition_stack.is_empty());
    assert_eq!(state.depth, 0);
    stats.output_ops = out.len();
    stats.abstractions = state.engine.abstractions;
    (out, stats)
}

pub(crate) fn caps() -> (usize, usize) { (DEGREE_CAP, MONOMIAL_CAP) }
