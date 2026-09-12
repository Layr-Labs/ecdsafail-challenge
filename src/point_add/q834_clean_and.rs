//! Streaming exact Boolean-value proof for measurement-assisted AND cleanup.
//!
//! IDs denote immutable Boolean functions; equality is a proof, inequality is
//! ignorance. Cache eviction only forgets identities. No sampled values enter
//! recognition. Inputs are explicitly supplied from the unchanged ABI.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT};
use std::collections::HashMap;

const CACHE_CAP: usize = 1_048_576;

fn configured_cache_cap() -> usize {
    // Experiment-only override; production always uses CACHE_CAP.
    #[cfg(test)]
    if let Some(raw) = std::env::var_os("CLEAN_AND_EXPERIMENT_CACHE_CAP") {
        let cap = raw
            .to_str()
            .expect("cache cap must be UTF-8")
            .parse::<usize>()
            .expect("cache cap must be an integer");
        assert!(
            matches!(cap, 65_536 | 131_072 | 262_144 | 1_048_576),
            "cache cap outside predeclared experiment ladder"
        );
        return cap;
    }
    CACHE_CAP
}
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Expr {
    Xor(u64, u64),
    And(u64, u64),
}

struct Values {
    next: u64,
    by_expr: HashMap<Expr, u64>,
    by_id: HashMap<u64, Expr>,
    cache_cap: usize,
    evictions: u64,
}
impl Values {
    fn new() -> Self {
        Self {
            next: 2,
            by_expr: HashMap::new(),
            by_id: HashMap::new(),
            cache_cap: configured_cache_cap(),
            evictions: 0,
        }
    }
    fn fresh(&mut self) -> u64 {
        let v = self.next;
        self.next = self.next.checked_add(2).expect("proof value ID overflow");
        v
    }
    fn intern(&mut self, expr: Expr) -> u64 {
        if let Some(v) = self.by_expr.get(&expr) {
            return *v;
        }
        if self.by_expr.len() >= self.cache_cap {
            // Existing IDs retain meaning, but their definitions are forgotten.
            // Never recycle IDs: this cannot manufacture an equality.
            self.by_expr.clear();
            self.by_id.clear();
            self.evictions += 1;
        }
        let v = self.fresh();
        self.by_expr.insert(expr, v);
        self.by_id.insert(v, expr);
        v
    }
    fn xor(&mut self, a: u64, b: u64) -> u64 {
        if a == b {
            return 0;
        }
        if a == (b ^ 1) {
            return 1;
        }
        if a < 2 {
            return b ^ a;
        }
        if b < 2 {
            return a ^ b;
        }
        let parity = (a ^ b) & 1;
        let a = a & !1;
        let b = b & !1;
        if let Some(Expr::Xor(x, y)) = self.by_id.get(&a) {
            if *x == b {
                return *y ^ parity;
            }
            if *y == b {
                return *x ^ parity;
            }
        }
        if let Some(Expr::Xor(x, y)) = self.by_id.get(&b) {
            if *x == a {
                return *y ^ parity;
            }
            if *y == a {
                return *x ^ parity;
            }
        }
        self.intern(Expr::Xor(a.min(b), a.max(b))) ^ parity
    }
    fn and(&mut self, a: u64, b: u64) -> u64 {
        if a == 0 || b == 0 || a == (b ^ 1) {
            return 0;
        }
        if a == 1 || a == b {
            return b;
        }
        if b == 1 {
            return a;
        }
        self.intern(Expr::And(a.min(b), a.max(b)))
    }
}

/// A replacement justified by the original CCX's control values. The proof
/// still consumes that original CCX exactly once; emitted replacements never
/// pass through `step` again.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SupportLowering {
    Keep,
    Drop,
    X,
    Cx(QubitId),
}
impl SupportLowering {
    pub(super) fn apply(self, original: Op) -> Option<Op> {
        match self {
            Self::Keep => Some(original),
            Self::Drop => None,
            Self::X | Self::Cx(_) => {
                let mut lowered = Op::empty();
                lowered.q_target = original.q_target;
                lowered.c_condition = original.c_condition;
                lowered.kind = K::X;
                if let Self::Cx(control) = self {
                    lowered.kind = K::CX;
                    lowered.q_control1 = control;
                }
                lowered.validate();
                Some(lowered)
            }
        }
    }
}

pub(super) struct Proof {
 pub residual_action:Option<(usize,bool)>,live:HashMap<u64,usize>, pub affine_allowed:bool,pub affine_counts:[[u64;2];5],pub affine_queries:u64,
    values: Values,
    q: Vec<u64>,
    c: Vec<u64>,
    condition: u64,
    stack: Vec<u64>,
    pub rewrites: u64,
    pub ccx_seen: u64,
    pub conditional_ccx: u64,
    pub support_lowering: SupportLowering,
    // Additional to the incumbent clean-AND cleanup, with q0 excluded.
    pub support_dead: u64,
    pub support_x: u64,
    pub support_cx: u64,
}
impl Proof {
    pub fn new(nq: usize, nb: usize, qinputs: &[usize], cinputs: &[usize]) -> Self {
        let mut s = Self {
            residual_action:None,live:HashMap::new(),affine_allowed:true,affine_counts:[[0;2];5],affine_queries:0,
            values: Values::new(),
            q: vec![0; nq],
            c: vec![0; nb],
            condition: 1,
            stack: Vec::new(),
            rewrites: 0,
            ccx_seen: 0,
            conditional_ccx: 0,
            support_lowering: SupportLowering::Keep,
            support_dead: 0,
            support_x: 0,
            support_cx: 0,
        };
        for &i in qinputs {
            s.q[i] = s.values.fresh();
        }
        for &i in cinputs {
            s.c[i] = s.values.fresh();
        }
        for q in 1..s.q.len(){if s.q[q]>=2{s.live.insert(s.q[q]&!1,q);}}
        s
    }
    pub fn evictions(&self) -> u64 {
        self.values.evictions
    }
    #[cfg(test)]
    pub fn cache_cap(&self) -> usize {
        self.values.cache_cap
    }
    pub fn balanced(&self) -> bool {
        self.stack.is_empty() && self.condition == 1
    }
    // Read-only admission query for the separately proved shared-product cell.
    // No new equality rule, cache policy, or clean-AND rewrite is introduced.
    pub(super) fn qubit_is_zero(&self, q: usize) -> bool {
        self.q[q] == 0
    }
    pub fn step(&mut self, op:&Op)->bool {
        self.residual_action=None;
        let t=op.q_target.0 as usize;
        let old=self.q.get(t).copied().map(|v|(t,v));
        let sw=if op.kind==K::Swap {Some((op.q_control1.0 as usize,self.q[op.q_control1.0 as usize]))}else{None};
        let rewritten=self.original_step(op);
        if self.affine_allowed && !rewritten && self.support_lowering==SupportLowering::Keep && op.kind==K::CCX && self.condition==1 && op.c_condition==NO_BIT && t!=0 && op.q_control1!=QubitId(0) && op.q_control2!=QubitId(0) && self.q[t]>=2 {
            self.affine_queries+=1;
            if let Some((w,p))=self.affine(self.q[t],t){self.affine_counts[w.len()][p as usize]+=1;if w.len()==1{self.residual_action=Some((w[0],p));}}
        }
        for (q,before) in [old,sw].into_iter().flatten(){let after=self.q[q];if before!=after{
            if self.live.get(&(before&!1))==Some(&q){self.live.remove(&(before&!1));}
            if q!=0 && after>=2{self.live.insert(after&!1,q);}
        }}
        rewritten
    }
    fn original_step(&mut self, op: &Op) -> bool {
        // Every input operation, including conditions, invalidates the prior
        // action. No stale CCX decision may affect the next emitted record.
        self.support_lowering = SupportLowering::Keep;
        if op.kind == K::PushCondition {
            self.stack.push(self.condition);
            self.condition = self
                .values
                .and(self.condition, self.c[op.c_condition.0 as usize]);
            return false;
        }
        if op.kind == K::PopCondition {
            self.condition = self.stack.pop().expect("proof condition stack underflow");
            return false;
        }
        let cond = if op.c_condition == NO_BIT {
            self.condition
        } else {
            self.values
                .and(self.condition, self.c[op.c_condition.0 as usize])
        };
        match op.kind {
            K::CCX => {
                op.validate();
                self.ccx_seen += 1;
                if cond != 1 {
                    self.conditional_ccx += 1;
                }
                let a = op.q_control1.0 as usize;
                let b = op.q_control2.0 as usize;
                let t = op.q_target.0 as usize;
                let product = self.values.and(self.q[a], self.q[b]);
                // q0 is the separately specialized outer control. Excluding it
                // makes each replacement save one post-specialization Toffoli.
                let rewrite = cond == 1 && a != 0 && b != 0 && t != 0 && self.q[t] == product;
                if !rewrite && cond == 1 && a != 0 && b != 0 && t != 0 {
                    self.support_lowering = if product == 0 {
                        self.support_dead += 1;
                        SupportLowering::Drop
                    } else if product == 1 {
                        self.support_x += 1;
                        SupportLowering::X
                    } else if product == self.q[a] {
                        self.support_cx += 1;
                        SupportLowering::Cx(op.q_control1)
                    } else if product == self.q[b] {
                        self.support_cx += 1;
                        SupportLowering::Cx(op.q_control2)
                    } else {
                        SupportLowering::Keep
                    };
                }
                let toggle = self.values.and(cond, product);
                self.q[t] = self.values.xor(self.q[t], toggle);
                if rewrite {
                    self.rewrites += 1;
                }
                return rewrite;
            }
            K::CX => {
                let t = op.q_target.0 as usize;
                let toggle = self.values.and(cond, self.q[op.q_control1.0 as usize]);
                self.q[t] = self.values.xor(self.q[t], toggle);
            }
            K::X => {
                let t = op.q_target.0 as usize;
                self.q[t] = self.values.xor(self.q[t], cond);
            }
            K::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                let delta = self.values.xor(self.q[a], self.q[b]);
                let toggle = self.values.and(cond, delta);
                self.q[a] = self.values.xor(self.q[a], toggle);
                self.q[b] = self.values.xor(self.q[b], toggle);
            }
            K::Hmr | K::R => {
                let t = op.q_target.0 as usize;
                self.q[t] = self.values.and(self.q[t], cond ^ 1);
                if op.kind == K::Hmr {
                    let b = op.c_target.0 as usize;
                    let measurement = self.values.fresh();
                    let old = self.values.and(self.c[b], cond ^ 1);
                    let new = self.values.and(measurement, cond);
                    self.c[b] = self.values.xor(old, new);
                }
            }
            K::BitInvert => {
                let b = op.c_target.0 as usize;
                self.c[b] = self.values.xor(self.c[b], cond);
            }
            K::BitStore0 => {
                let b = op.c_target.0 as usize;
                self.c[b] = self.values.and(self.c[b], cond ^ 1);
            }
            K::BitStore1 => {
                let b = op.c_target.0 as usize;
                let old = self.values.and(self.c[b], cond ^ 1);
                self.c[b] = self.values.xor(old, cond);
            }
            K::Z | K::CZ | K::CCZ | K::Neg | K::AppendToRegister | K::Register | K::DebugPrint => {}
            K::PushCondition | K::PopCondition => unreachable!(),
        }
        false
    }
}

pub(super) fn replacement(op: &Op, measurement_bit: BitId) -> [Op; 2] {
    assert_eq!(op.kind, K::CCX);
    let mut h = Op::empty();
    h.kind = K::Hmr;
    h.q_target = op.q_target;
    h.c_target = measurement_bit;
    let mut z = Op::empty();
    z.kind = K::CZ;
    z.q_control1 = op.q_control1;
    z.q_target = op.q_control2;
    z.c_condition = measurement_bit;
    [h, z]
}

#[cfg(test)]
mod tests {
    use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;

    #[test]
    fn production_default_cache_capacity_is_1048576() {
        assert_eq!(super::CACHE_CAP, 1_048_576);
        if std::env::var_os("CLEAN_AND_EXPERIMENT_CACHE_CAP").is_none() {
            assert_eq!(super::configured_cache_cap(), 1_048_576);
        }
    }

    // This adapter applies the same streaming proof and rewrite as HIR emission.
    fn optimize(ops: &[Op], nq: usize, inputs: &[usize]) -> Vec<Op> {
        let mut proof = super::Proof::new(nq, 2, inputs, &[0]);
        let mut out = Vec::new();
        for op in ops {
            if proof.step(op) {
                out.extend(super::replacement(op, BitId(1)));
            } else if let Some(lowered) = proof.support_lowering.apply(*op) {
                out.push(lowered);
            }
        }
        out
    }
    fn gate(k: K, a: usize, b: usize, t: usize) -> Op {
        let mut o = Op::empty();
        o.kind = k;
        o.q_target = QubitId(t as u64);
        if matches!(k, K::CX | K::CZ | K::Swap | K::CCX | K::CCZ) {
            o.q_control1 = QubitId(a as u64);
        }
        if matches!(k, K::CCX | K::CCZ) {
            o.q_control2 = QubitId(b as u64);
        }
        o
    }
    struct Outcomes(u64);
    impl XofReader for Outcomes {
        fn read(&mut self, b: &mut [u8]) {
            let value = if self.0 & 1 == 1 { 255 } else { 0 };
            b.fill(value);
            self.0 >>= 1;
        }
    }
    fn run(ops: &[Op], values: &[bool], classical: bool, outcome: u64) -> (Vec<u64>, u64) {
        let mut rng = Outcomes(outcome);
        let mut sim = Simulator::new(values.len(), 2, &mut rng);
        for (q, v) in sim.qubits.iter_mut().zip(values) {
            *q = u64::from(*v);
        }
        sim.bits[0] = u64::from(classical);
        sim.apply_iter(ops.iter());
        (sim.qubits.iter().map(|v| v & 1).collect(), sim.phase & 1)
    }
    fn assert_exact(base: &[Op], transformed: &[Op], nq: usize, inputs: &[usize]) {
        for mask in 0..(1 << inputs.len()) {
            for c in [false, true] {
                for m in 0..(1u64 << hmrs(transformed)) {
                    let mut values = vec![false; nq];
                    for (i, q) in inputs.iter().enumerate() {
                        values[*q] = (mask >> i) & 1 == 1;
                    }
                    assert_eq!(
                        run(base, &values, c, m),
                        run(transformed, &values, c, m),
                        "basis={mask} classical={c} outcome={m}"
                    );
                }
            }
        }
    }
    fn hmrs(ops: &[Op]) -> usize {
        ops.iter().filter(|o| o.kind == K::Hmr).count()
    }
    #[test]
    fn clean_target_controls_used_and_restored_exact_phase() {
        let ops = vec![
            gate(K::CCX, 1, 2, 3),
            gate(K::CZ, 3, 0, 4),
            gate(K::CX, 3, 0, 4),
            gate(K::X, 0, 0, 1),
            gate(K::X, 0, 0, 1),
            gate(K::CCX, 1, 2, 3),
        ];
        let out = optimize(&ops, 5, &[1, 2, 4]);
        assert_eq!(
            hmrs(&out),
            1,
            "the proved clean AND clearing CCX must become HMR"
        );
        assert_eq!(out.iter().filter(|o| o.kind == K::CCX).count(), 1);
        assert_exact(&ops, &out, 5, &[1, 2, 4]);
    }
    #[test]
    fn dirty_target_negative_control() {
        let ops = vec![
            gate(K::CCX, 1, 2, 3),
            gate(K::CX, 3, 0, 4),
            gate(K::CCX, 1, 2, 3),
        ];
        let out = optimize(&ops, 5, &[1, 2, 3, 4]);
        assert_eq!(hmrs(&out), 0);
        assert_exact(&ops, &out, 5, &[1, 2, 3, 4]);
        // Directly replacing this dirty-target clearing is observably wrong.
        let mut bad = ops[..2].to_vec();
        let mut h = gate(K::Hmr, 0, 0, 3);
        h.c_target = BitId(1);
        bad.push(h);
        let mut z = gate(K::CZ, 1, 0, 2);
        z.c_condition = BitId(1);
        bad.push(z);
        assert_ne!(
            run(&ops, &[false, false, false, true, false], false, 0),
            run(&bad, &[false, false, false, true, false], false, 0)
        );
    }
    #[test]
    fn changed_control_negative_and_phase_witness() {
        let ops = vec![
            gate(K::CCX, 1, 2, 3),
            gate(K::X, 0, 0, 1),
            gate(K::CCX, 1, 2, 3),
        ];
        let out = optimize(&ops, 4, &[1, 2]);
        assert_eq!(hmrs(&out), 0);
        assert_exact(&ops, &out, 4, &[1, 2]);
    }
    #[test]
    fn conditional_mismatch_is_conservatively_rejected() {
        let mut clear = gate(K::CCX, 1, 2, 3);
        clear.c_condition = BitId(0);
        let ops = vec![gate(K::CCX, 1, 2, 3), clear];
        let out = optimize(&ops, 4, &[1, 2]);
        assert_eq!(hmrs(&out), 0);
        assert_exact(&ops, &out, 4, &[1, 2]);
    }
    #[test]
    fn descending_v_chain_exhaustive() {
        for controls in 3..=7 {
            let first = controls + 1;
            let target = 2 * controls - 1;
            let nq = target + 1;
            let mut ops = vec![gate(K::CCX, 1, 2, first)];
            for i in 3..controls {
                ops.push(gate(K::CCX, first + i - 3, i, first + i - 2));
            }
            ops.push(gate(K::CCX, first + controls - 3, controls, target));
            for i in (3..controls).rev() {
                ops.push(gate(K::CCX, first + i - 3, i, first + i - 2));
            }
            ops.push(gate(K::CCX, 1, 2, first));
            let inputs: Vec<_> = (1..=controls).chain([target]).collect();
            let out = optimize(&ops, nq, &inputs);
            assert_eq!(hmrs(&out), controls - 2);
            assert_eq!(
                out.iter().filter(|o| o.kind == K::CCX).count(),
                controls - 1
            );
            assert_exact(&ops, &out, nq, &inputs);
        }
    }
    #[test]
    fn existing_measurement_and_condition_stack_do_not_leak_facts() {
        let mut h = gate(K::Hmr, 0, 0, 3);
        h.c_target = BitId(0);
        let mut push = Op::empty();
        push.kind = K::PushCondition;
        push.c_condition = BitId(0);
        let mut pop = Op::empty();
        pop.kind = K::PopCondition;
        let ops = vec![
            gate(K::CCX, 1, 2, 3),
            h,
            push,
            gate(K::CCX, 1, 2, 3),
            pop,
            gate(K::CCX, 1, 2, 3),
        ];
        let out = optimize(&ops, 4, &[1, 2]);
        assert_eq!(hmrs(&out), 1);
        assert_exact(&ops, &out, 4, &[1, 2]);
        assert_eq!(out.last().unwrap().c_condition, NO_BIT);
    }
    #[test]
    fn value_ids_remain_sound_across_cache_evictions() {
        let mut values = super::Values::new();
        values.cache_cap = 8;
        let mut pool = vec![(0u64, 0u8), (1, 255)];
        for truth in [0b10101010, 0b11001100, 0b11110000] {
            pool.push((values.fresh(), truth));
        }
        let mut meanings = std::collections::HashMap::new();
        let mut seed = 0x12345678u64;
        for _ in 0..20000 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            pool.push((values.fresh(), (seed >> 17) as u8));
            let a = pool[(seed as usize) % pool.len()];
            let b = pool[((seed >> 32) as usize) % pool.len()];
            let (id, truth) = if seed & 1 == 0 {
                (values.and(a.0, b.0), a.1 & b.1)
            } else {
                (values.xor(a.0, b.0), a.1 ^ b.1)
            };
            for (key, value) in [(id, truth), (id ^ 1, !truth)] {
                if let Some(old) = meanings.insert(key, value) {
                    assert_eq!(old, value, "false equality for proof ID {key}");
                }
            }
            pool.push((id, truth));
            while pool.len() > 40 {
                pool.remove(5);
            }
        }
        assert!(values.evictions > 100);
    }
    #[test]
    fn condition_stack_snapshots_values_before_classical_write() {
        let mut proof = super::Proof::new(4, 2, &[1, 2], &[0]);
        let mut push = Op::empty();
        push.kind = K::PushCondition;
        push.c_condition = BitId(0);
        proof.step(&push);
        let snapshot = proof.condition;
        let mut invert = Op::empty();
        invert.kind = K::BitInvert;
        invert.c_target = BitId(0);
        proof.step(&invert);
        assert_eq!(proof.condition, snapshot);
        assert_ne!(proof.c[0], snapshot);
        let clear = gate(K::CCX, 1, 2, 3);
        assert!(!proof.step(&clear));
    }
    #[test]
    fn missing_phase_correction_has_a_decisive_witness() {
        let base = vec![gate(K::CCX, 1, 2, 3), gate(K::CCX, 1, 2, 3)];
        let out = optimize(&base, 4, &[1, 2]);
        let mut bad = out.clone();
        bad.pop();
        let input = [false, true, true, false];
        assert_eq!(run(&base, &input, false, 1), run(&out, &input, false, 1));
        assert_ne!(run(&base, &input, false, 1), run(&bad, &input, false, 1));
    }
}

// Read-only test diagnostic; original proof methods and cache policy are unchanged.
#[cfg(test)]
impl Proof {
 pub(super) fn diagnostic_fingerprint(&self)->String {
  use sha3::{Digest,Sha3_256};let mut h=Sha3_256::new();
  for &v in self.q.iter().chain(self.c.iter()).chain(self.stack.iter()){h.update(v.to_le_bytes());}
  for v in [self.values.next,self.values.evictions,self.values.cache_cap as u64,self.condition,self.rewrites,self.ccx_seen,self.conditional_ccx,self.support_dead,self.support_x,self.support_cx]{h.update(v.to_le_bytes());}
  let mut rows:Vec<_>=self.values.by_id.iter().map(|(&id,&e)|{let(t,a,b)=match e{Expr::Xor(a,b)=>(0u64,a,b),Expr::And(a,b)=>(1u64,a,b)};(id,t,a,b)}).collect();rows.sort_unstable();
  for (id,t,a,b) in rows{for v in [id,t,a,b]{h.update(v.to_le_bytes());}}
  format!("{{\"sha3_256\":\"{:x}\",\"next\":{},\"evictions\":{},\"entries\":{},\"cap\":{}}}",h.finalize(),self.values.next,self.values.evictions,self.values.by_id.len(),self.values.cache_cap)
 }
}

// Read-only query on the outgoing state of the original CCX, after old priorities.
impl Proof {
 pub(super) fn ccx_result_is_one(&self, op:&Op)->bool {
  op.kind==K::CCX && op.c_condition==NO_BIT && self.condition==1 &&
  op.q_target!=QubitId(0) && op.q_control1!=QubitId(0) && op.q_control2!=QubitId(0) &&
  self.support_lowering==SupportLowering::Keep && self.q[op.q_target.0 as usize]==1
 }
}
pub(super) fn replacement_to_one(op:&Op, measurement_bit:BitId)->[Op;4] {
 let [h,z]=replacement(op,measurement_bit);
 let mut neg=Op::empty();neg.kind=K::Neg;neg.c_condition=measurement_bit;
 let mut x=Op::empty();x.kind=K::X;x.q_target=op.q_target;
 [h,z,neg,x]
}

impl Proof {
 fn affine(&self,value:u64,target:usize)->Option<(Vec<usize>,bool)>{
  let mut terms=Vec::new();let mut parity=false;let mut visited=0;
  self.affine_visit(value,target,0,&mut visited,&mut terms,&mut parity)?;
  terms.sort_unstable();let mut out=Vec::new();for w in terms {if out.last()==Some(&w){out.pop();}else{out.push(w);}}
  if out.len()>4{return None;}Some((out,parity))
 }
 fn affine_visit(&self,value:u64,target:usize,depth:usize,visited:&mut usize,terms:&mut Vec<usize>,parity:&mut bool)->Option<()> {
  *visited+=1;if *visited>24{return None;}
  *parity^=value&1!=0;let id=value&!1;if id==0{return Some(());}
  if let Some(&q)=self.live.get(&id){if q!=0 && q!=target && self.q.get(q).map(|v|v&!1)==Some(id){terms.push(q);*parity^=self.q[q]&1!=0;return Some(());}}
  if depth>=4{return None;}
  match self.values.by_id.get(&id)? {Expr::Xor(a,b)=>{self.affine_visit(*a,target,depth+1,visited,terms,parity)?;self.affine_visit(*b,target,depth+1,visited,terms,parity)},Expr::And(..)=>None}
 }
}
#[cfg(test)]
mod affine_tests {
 use super::*;
 #[test]fn exact_linear_representation_and_forgetting(){
  let mut p=Proof::new(10,1,&[1,2,3,4,5,6],&[]);let a=p.q[1];let b=p.q[2];let ab=p.values.xor(a,b);let abc=p.values.xor(ab,p.q[3]);
  assert_eq!(p.affine(abc^1,9),Some((vec![1,2,3],true)));
  p.q[7]=abc^1;p.live.insert(abc&!1,7);assert_eq!(p.affine(abc,9),Some((vec![7],true)));
  p.q[7]=0;assert_eq!(p.affine(abc,9),Some((vec![1,2,3],false)));
  p.values.by_id.clear();assert_eq!(p.affine(abc,9),None);
  assert_eq!(p.affine(a,1),None);p.live.insert(a&!1,0);assert_eq!(p.affine(a,9),None);
 }
 #[test]fn cancellation_is_parity_not_set_union(){
  let mut p=Proof::new(10,1,&[1,2,3],&[]);let a=p.q[1];let b=p.q[2];let c=p.q[3];let ab=p.values.xor(a,b);let ac=p.values.xor(a,c);let x=p.values.xor(ab,ac);
  assert_eq!(p.affine(x,9),Some((vec![2,3],false)));
  let and=p.values.and(a,b);assert_eq!(p.affine(and,9),None);p.q[4]=and;p.live.insert(and,4);assert_eq!(p.affine(and,9),Some((vec![4],false)));
 }
}
#[cfg(test)]
mod affine_native_phase {
 use super::*;
 use crate::sim::Simulator;
 use sha3::digest::XofReader;
 struct Outcome(u8);impl XofReader for Outcome{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
 fn gate(k:K,a:usize,b:usize,t:usize)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t as u64);if matches!(k,K::CX|K::CZ|K::CCX){o.q_control1=QubitId(a as u64);}if k==K::CCX{o.q_control2=QubitId(b as u64);}o}
 #[test]fn native_multiterm_all_basis_phase_and_conditions(){
  let mut cases=0;
  for n in 1..=4{for parity in [false,true]{for active in [false,true]{for m in [0,255]{
   let target=7;let mut replacement=Vec::new();let mut h=gate(K::Hmr,0,0,target);h.c_target=BitId(1);replacement.push(h);
   let mut z=gate(K::CZ,1,0,2);z.c_condition=BitId(1);replacement.push(z);
   for q in 3..3+n{let mut z=gate(K::Z,0,0,q);z.c_condition=BitId(1);replacement.push(z);}
   if parity{let mut z=Op::empty();z.kind=K::Neg;z.c_condition=BitId(1);replacement.push(z);}
   for q in 3..3+n{replacement.push(gate(K::CX,q,0,target));}if parity{replacement.push(gate(K::X,0,0,target));}
   let mut push=Op::empty();push.kind=K::PushCondition;push.c_condition=BitId(0);let mut pop=Op::empty();pop.kind=K::PopCondition;
   replacement.insert(0,push);replacement.push(pop);
   let mut old=gate(K::CCX,1,2,target);old.c_condition=BitId(0);
   for mask in 0..(1<<(n+2)){for stale in 0..2u64{
    let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(9,2,&mut ra);let mut b=Simulator::new(9,2,&mut rb);
    for q in 1..3+n{a.qubits[q]=(mask>>(q-1))&1;}let mut residual=u64::from(parity);for q in 3..3+n{residual^=a.qubits[q];}a.qubits[target]=residual^(a.qubits[1]&a.qubits[2]);a.qubits[8]=mask&1;
    a.bits[0]=u64::from(active);a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();
    a.apply_iter([old].iter());b.apply_iter(replacement.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits[0],b.bits[0]);cases+=1;
   }}
  }}}}
  assert_eq!(cases,1920);
 }
}

pub(super)fn replacement_to_wire(op:&Op,bit:BitId,wire:QubitId,parity:bool)->Vec<Op>{
 assert_ne!(wire,op.q_target);assert_ne!(wire,QubitId(0));
 let [h,cz]=replacement(op,bit);let mut z=Op::empty();z.kind=K::Z;z.q_target=wire;z.c_condition=bit;
 let mut cx=Op::empty();cx.kind=K::CX;cx.q_control1=wire;cx.q_target=op.q_target;
 let mut out=vec![h,cz,z];if parity{let mut n=Op::empty();n.kind=K::Neg;n.c_condition=bit;out.push(n);}out.push(cx);
 if parity{let mut x=Op::empty();x.kind=K::X;x.q_target=op.q_target;out.push(x);}for o in &out{o.validate();}out
}
#[cfg(test)]mod wire_action_tests{
use super::*;
fn gate(k:K,a:usize,b:usize,t:usize)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t as u64);if matches!(k,K::CX|K::CCX){o.q_control1=QubitId(a as u64);}if k==K::CCX{o.q_control2=QubitId(b as u64);}o}
#[test]fn wire_action_refresh_permission_stale_and_no_multiterm(){
 for mode in 0..4{let mut p=Proof::new(8,1,&[1,2,3,5],&[]);p.step(&gate(K::CCX,1,2,4));p.step(&gate(K::CX,3,0,4));match mode{1=>p.affine_allowed=false,2=>{p.live.insert(p.q[3]&!1,6);},3=>{p.step(&gate(K::CX,5,0,4));},_=>{}}
 p.step(&gate(K::CCX,1,2,4));assert_eq!(p.residual_action,if mode==0{Some((3,false))}else{None});p.step(&gate(K::X,0,0,7));assert_eq!(p.residual_action,None);
 }
}
}

// Exact read-only counterpart of Values::and; never interns, allocates IDs, or changes cache.
impl Proof {
 pub(super) fn retention_product(&self,t:usize,a:usize,b:usize)->(bool,u8){
  if self.condition!=1{return(false,0)}
  let(a,b)=(self.q[a],self.q[b]);
  let product=if a==0||b==0||a==(b^1){Some(0)}else if a==1||a==b{Some(b)}else if b==1{Some(a)}else{self.values.by_expr.get(&Expr::And(a.min(b),a.max(b))).copied()};
  let Some(p)=product else{return(false,0)};let kind=if p==0{1}else if p==1{2}else if p==a||p==b{3}else{4};(self.q[t]==p,kind)
 }
}

