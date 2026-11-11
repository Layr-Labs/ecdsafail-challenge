//! Exact, bounded ROBDD support for final Toffoli reductions.
//!
//! Each immutable BDD atom is an unknown Boolean function. Failed bounded
//! operations become a fresh atom for their entire result: no partial proof
//! is retained. Canonical node equality therefore proves a universal identity
//! even when the represented input functions are correlated. Periodic rebasing
//! forgets relationships while preserving equal functions and constants.
//!
//! The pass interprets the original stream, preserves measurement/reset and
//! phase operations, and only drops a provably inactive CCX or replaces one by
//! a CX with the same target, classical condition, and stack position.
//!
//! Local validation: exhaustive comparison on 64 randomized circuits, each on
//! all 512 input/measurement assignments, including conditions and phase gates.
use crate::circuit::{analyze_ops, Op, OperationType as K, QubitOrBit, NO_BIT, NO_QUBIT};
use std::collections::HashMap;
#[derive(Clone, Copy)]
struct Node {
    v: u32,
    lo: u32,
    hi: u32,
}
struct Bdd {
    nodes: Vec<Node>,
    unique: HashMap<(u32, u32, u32), u32>,
    var: u32,
    budget: usize,
}
impl Bdd {
    fn new() -> Self {
        Self {
            nodes: vec![
                Node {
                    v: u32::MAX,
                    lo: 0,
                    hi: 0
                };
                2
            ],
            unique: HashMap::new(),
            var: 0,
            budget: 64,
        }
    }
    fn node(&mut self, v: u32, lo: u32, hi: u32) -> u32 {
        if lo == hi {
            return lo;
        }
        let key = (v, lo, hi);
        if let Some(&x) = self.unique.get(&key) {
            return x;
        }
        let x = self.nodes.len() as u32;
        self.nodes.push(Node { v, lo, hi });
        self.unique.insert(key, x);
        x
    }
    fn fresh(&mut self) -> u32 {
        self.var += 1;
        self.node(self.var, 0, 1)
    }
    fn rec(
        &mut self,
        mut a: u32,
        mut b: u32,
        xor: bool,
        cache: &mut HashMap<(u32, u32), u32>,
        fuel: &mut usize,
    ) -> Option<u32> {
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        if a == 0 {
            return Some(if xor { b } else { 0 });
        }
        if a == b {
            return Some(if xor { 0 } else { a });
        }
        if !xor && a == 1 {
            return Some(b);
        }
        if b < 2 {
            return Some(if xor { a ^ b } else { a & b });
        }
        if let Some(&x) = cache.get(&(a, b)) {
            return Some(x);
        }
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        let na = self.nodes[a as usize];
        let nb = self.nodes[b as usize];
        let v = na.v.min(nb.v);
        let (al, ah) = if na.v == v { (na.lo, na.hi) } else { (a, a) };
        let (bl, bh) = if nb.v == v { (nb.lo, nb.hi) } else { (b, b) };
        let lo = self.rec(al, bl, xor, cache, fuel)?;
        let hi = self.rec(ah, bh, xor, cache, fuel)?;
        let n = self.node(v, lo, hi);
        cache.insert((a, b), n);
        Some(n)
    }
    fn apply(&mut self, a: u32, b: u32, xor: bool) -> u32 {
        let mut fuel = self.budget;
        self.rec(a, b, xor, &mut HashMap::new(), &mut fuel)
            .unwrap_or_else(|| self.fresh())
    }
    fn and(&mut self, a: u32, b: u32) -> u32 {
        self.apply(a, b, false)
    }
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        self.apply(a, b, true)
    }
    fn not(&mut self, a: u32) -> u32 {
        self.xor(a, 1)
    }
}
pub fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let mut d = Bdd::new();
    d.budget = 16;
    let mut q = vec![0; nq as usize];
    let mut bits = vec![0; nb as usize];
    for r in regs {
        for x in r {
            match x {
                QubitOrBit::Qubit(i) => q[i.0 as usize] = d.fresh(),
                QubitOrBit::Bit(i) => bits[i.0 as usize] = d.fresh(),
            }
        }
    }
    let mut cond = 1;
    let mut stack = vec![];
    let mut out = Vec::with_capacity(ops.len());
    let mut saved = 0;
    for (i, o) in ops.into_iter().enumerate() {
        if i > 0 && i % 100000 == 0 {
            let budget = d.budget;
            let mut nd = Bdd::new();
            nd.budget = budget;
            let mut remap = HashMap::from([(0, 0), (1, 1)]);
            for x in q
                .iter_mut()
                .chain(bits.iter_mut())
                .chain(stack.iter_mut())
                .chain(std::iter::once(&mut cond))
            {
                *x = *remap.entry(*x).or_insert_with(|| nd.fresh());
            }
            d = nd;
        }
        if o.kind == K::PushCondition {
            stack.push(cond);
            cond = d.and(cond, bits[o.c_condition.0 as usize]);
            out.push(o);
            continue;
        }
        if o.kind == K::PopCondition {
            cond = stack.pop().unwrap();
            out.push(o);
            continue;
        }
        let mut en = cond;
        if o.c_condition != NO_BIT {
            en = d.and(en, bits[o.c_condition.0 as usize]);
        }
        let (t, a, b) = (
            o.q_target.0 as usize,
            o.q_control1.0 as usize,
            o.q_control2.0 as usize,
        );
        let mut emit = Some(o);
        match o.kind {
            K::CCX => {
                let ab = d.and(q[a], q[b]);
                let toggle = d.and(en, ab);
                let ca = d.and(en, q[a]);
                let cb = d.and(en, q[b]);
                if toggle == 0 {
                    emit = None;
                    saved += 1;
                } else if toggle == ca || toggle == cb {
                    let mut p = o;
                    p.kind = K::CX;
                    p.q_control1 = if toggle == ca {
                        o.q_control1
                    } else {
                        o.q_control2
                    };
                    p.q_control2 = NO_QUBIT;
                    emit = Some(p);
                    saved += 1;
                    eprintln!("BDD rewrite index={i} controls={a},{b} target={t} condition={} stack={} replacement={}",o.c_condition.0,stack.len(),p.q_control1.0);
                }
                q[t] = d.xor(q[t], toggle);
            }
            K::CX => {
                let delta = d.and(en, q[a]);
                q[t] = d.xor(q[t], delta);
            }
            K::X => q[t] = d.xor(q[t], en),
            K::Swap => {
                let diff = d.xor(q[t], q[a]);
                let delta = d.and(en, diff);
                q[t] = d.xor(q[t], delta);
                q[a] = d.xor(q[a], delta);
            }
            K::Hmr => {
                let c = o.c_target.0 as usize;
                let fresh = d.fresh();
                let diff = d.xor(bits[c], fresh);
                let delta = d.and(en, diff);
                bits[c] = d.xor(bits[c], delta);
                let ne = d.not(en);
                q[t] = d.and(q[t], ne);
            }
            K::R => {
                let ne = d.not(en);
                q[t] = d.and(q[t], ne);
            }
            K::BitInvert => {
                let c = o.c_target.0 as usize;
                bits[c] = d.xor(bits[c], en);
            }
            K::BitStore0 => {
                let c = o.c_target.0 as usize;
                let ne = d.not(en);
                bits[c] = d.and(bits[c], ne);
            }
            K::BitStore1 => {
                let c = o.c_target.0 as usize;
                let ne = d.not(en);
                let old = d.not(bits[c]);
                let z = d.and(old, ne);
                bits[c] = d.not(z);
            }
            _ => {}
        }
        if let Some(p) = emit {
            p.validate();
            out.push(p);
        }
    }
    eprintln!("BDD reductions {saved}");
    out
}
