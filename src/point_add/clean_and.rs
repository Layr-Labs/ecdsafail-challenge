//! Streaming exact Boolean-value proof for measurement-assisted AND cleanup.
//!
//! IDs denote immutable Boolean functions; equality is a proof, inequality is
//! ignorance. Cache eviction only forgets identities. No sampled values enter
//! recognition. Inputs are explicitly supplied from the unchanged ABI.
use crate::circuit::{BitId, Op, OperationType as K, NO_BIT};
use std::collections::HashMap;

const CACHE_CAP: usize = 2_097_152;

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
            matches!(
                cap,
                65_536 | 131_072 | 262_144 | 1_048_576 | 2_097_152 | 4_194_304 | 8_388_608
            ),
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

pub(super) struct Proof {
    values: Values,
    q: Vec<u64>,
    c: Vec<u64>,
    condition: u64,
    stack: Vec<u64>,
    pub rewrites: u64,
    pub ccx_seen: u64,
    pub conditional_ccx: u64,
}
impl Proof {
    pub fn new(nq: usize, nb: usize, qinputs: &[usize], cinputs: &[usize]) -> Self {
        let mut s = Self {
            values: Values::new(),
            q: vec![0; nq],
            c: vec![0; nb],
            condition: 1,
            stack: Vec::new(),
            rewrites: 0,
            ccx_seen: 0,
            conditional_ccx: 0,
        };
        for &i in qinputs {
            s.q[i] = s.values.fresh();
        }
        for &i in cinputs {
            s.c[i] = s.values.fresh();
        }
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
    pub fn step(&mut self, op: &Op) -> bool {
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
    use quantum_ecc::sim::Simulator;
    use sha3::digest::XofReader;

    #[test]
    fn production_default_cache_capacity_is_2097152() {
        assert_eq!(super::CACHE_CAP, 2_097_152);
        if std::env::var_os("CLEAN_AND_EXPERIMENT_CACHE_CAP").is_none() {
            assert_eq!(super::configured_cache_cap(), 2_097_152);
        }
    }

    // This adapter applies the same streaming proof and rewrite as HIR emission.
    fn optimize(ops: &[Op], nq: usize, inputs: &[usize]) -> Vec<Op> {
        let mut proof = super::Proof::new(nq, 2, inputs, &[0]);
        let mut out = Vec::new();
        for op in ops {
            if proof.step(op) {
                out.extend(super::replacement(op, BitId(1)));
            } else {
                out.push(*op);
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
