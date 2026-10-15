//! I25: exact CCX support identities with immutable nonlinear interning. An atom denotes a Boolean
//! function at its creation boundary, never a mutable wire or classical bit.
//! Unknown products and oversized expressions get fresh, non-reused atoms.

use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit, NO_BIT};

fn atom_cap()->usize {128}
fn product_cap()->usize {1000000}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Affine {
    constant: bool,
    atoms: Vec<u64>,
}

impl Affine {
    fn constant(value: bool) -> Self {
        Self {
            constant: value,
            atoms: Vec::new(),
        }
    }

    fn is_zero(&self) -> bool {
        !self.constant && self.atoms.is_empty()
    }

    fn is_one(&self) -> bool {
        self.constant && self.atoms.is_empty()
    }

    fn complement(&self) -> Self {
        Self {
            constant: !self.constant,
            atoms: self.atoms.clone(),
        }
    }

    fn complements(&self, other: &Self) -> bool {
        self.constant != other.constant && self.atoms == other.atoms
    }
}

pub(super) enum Rewrite {
    Keep,
    Drop,
    X,
    Cx(QubitId),
}

impl Rewrite {
    pub(super) fn emit(self, op: Op, result: &mut Vec<Op>) {
        match self {
            Rewrite::Keep => result.push(op),
            Rewrite::Drop => {}
            rewrite => {
                let mut replacement = Op::empty();
                replacement.q_target = op.q_target;
                replacement.c_condition = op.c_condition;
                match rewrite {
                    Rewrite::X => replacement.kind = OperationType::X,
                    Rewrite::Cx(control) => {
                        replacement.kind = OperationType::CX;
                        replacement.q_control1 = control;
                    }
                    _ => unreachable!(),
                }
                replacement.validate();
                result.push(replacement);
            }
        }
    }
}

pub(super) struct Support {
    qubits: Vec<Affine>,
    bits: Vec<Affine>,
    base_condition: Affine,
    condition_stack: Vec<Affine>,
    next_atom: u64,
    products: std::collections::HashMap<(Vec<u64>,Vec<u64>),u64>,
    factors: Vec<Vec<u64>>,
    monomial_products: std::collections::HashMap<Vec<u64>,u64>,
    large_xors: std::collections::HashMap<Vec<u64>,u64>,
}

impl Support {
    pub(super) fn new(ops: &[Op]) -> Self {
        let (nq, nb, _, registers) = analyze_ops(ops.iter());
        let mut quantum_inputs = vec![false; nq as usize];
        let mut classical_inputs = vec![false; nb as usize];
        for register in registers {
            for slot in register {
                match slot {
                    QubitOrBit::Qubit(q) => quantum_inputs[q.0 as usize] = true,
                    QubitOrBit::Bit(b) => classical_inputs[b.0 as usize] = true,
                }
            }
        }
        let mut state = Self {
            qubits: vec![Affine::constant(false); nq as usize],
            bits: vec![Affine::constant(false); nb as usize],
            base_condition: Affine::constant(true),
            condition_stack: Vec::new(),
            next_atom: 0,
            products: std::collections::HashMap::new(),
            factors: Vec::new(),
            monomial_products: std::collections::HashMap::new(),
            large_xors: std::collections::HashMap::new(),
        };
        // Both kinds of ABI slot are unknown. Repeated annotations for one
        // physical slot still describe the same value.
        for (q, input) in quantum_inputs.into_iter().enumerate() {
            if input {
                state.qubits[q] = state.fresh();
            }
        }
        for (b, input) in classical_inputs.into_iter().enumerate() {
            if input {
                state.bits[b] = state.fresh();
            }
        }
        state
    }

    fn fresh(&mut self) -> Affine {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("affine atom identifier overflow");
        assert_eq!(id as usize,self.factors.len());
        self.factors.push(vec![id]);
        Affine {
            constant: false,
            atoms: vec![id],
        }
    }

    fn xor(&mut self, a: &Affine, b: &Affine) -> Affine {
        let mut atoms = Vec::with_capacity(a.atoms.len() + b.atoms.len());
        let (mut i, mut j) = (0, 0);
        while i < a.atoms.len() || j < b.atoms.len() {
            if j == b.atoms.len() || (i < a.atoms.len() && a.atoms[i] < b.atoms[j]) {
                atoms.push(a.atoms[i]);
                i += 1;
            } else if i == a.atoms.len() || b.atoms[j] < a.atoms[i] {
                atoms.push(b.atoms[j]);
                j += 1;
            } else {
                i += 1;
                j += 1;
            }
        }
        if atoms.len() > atom_cap() {
            // This fresh atom represents the entire XOR, including its
            // constant. It must not be mistaken for zero or an older atom.
            self.retain_large(a.constant^b.constant,atoms)
        } else {
            Affine {
                constant: a.constant ^ b.constant,
                atoms,
            }
        }
    }

    fn and(&mut self, a: &Affine, b: &Affine) -> Affine {
        if a.is_zero() || b.is_zero() || a.complements(b) {
            Affine::constant(false)
        } else if a.is_one() {
            b.clone()
        } else if b.is_one() || a == b {
            a.clone()
        } else if a.atoms.len()*b.atoms.len() <= 64 {
            // Exact ANF expansion: immutable monomials are square-free sets
            // of opaque base Boolean functions. Idempotence and distributivity
            // hold even when a base function is not an independent variable.
            let mut terms=std::collections::BTreeSet::<u64>::new();
            let mut toggle=|id| {if !terms.insert(id){terms.remove(&id);}};
            if a.constant {for &id in &b.atoms {toggle(id);}}
            if b.constant {for &id in &a.atoms {toggle(id);}}
            for &x in &a.atoms {for &y in &b.atoms {
                let mut factors=self.factors[x as usize].clone();
                factors.extend_from_slice(&self.factors[y as usize]);
                factors.sort_unstable();factors.dedup();
                if self.monomial_products.len()>=product_cap(){self.monomial_products.clear();}
                let id=if factors.len()>128 {self.fresh().atoms[0]}
                    else if factors.len()==1 {factors[0]}
                    else if let Some(&id)=self.monomial_products.get(&factors){id}
                    else {let id=self.fresh().atoms[0];self.factors[id as usize]=factors.clone();self.monomial_products.insert(factors,id);id};
                toggle(id);
            }}
            let atoms:Vec<_>=terms.into_iter().collect();
            if atoms.len()>atom_cap(){self.retain_large(a.constant&&b.constant,atoms)}else{Affine{constant:a.constant&&b.constant,atoms}}
        } else {
            // Keys denote complete immutable Boolean expressions, never wire
            // slots. HashMap checks exact key equality, not just a hash value.
            // (A^ca)(B^cb) = AB ^ ca*B ^ cb*A ^ ca*cb.
            let ca=a.constant; let cb=b.constant;
            let aa=Affine {constant:false, atoms:a.atoms.clone()};
            let bb=Affine {constant:false, atoms:b.atoms.clone()};
            let mut linear=Affine::constant(ca && cb);
            if ca {linear=self.xor(&linear,&bb);}
            if cb {linear=self.xor(&linear,&aa);}
            let mut left=aa.atoms;let mut right=bb.atoms;
            if left>right {std::mem::swap(&mut left,&mut right);}
            let key=(left,right);
            let id=if let Some(&id)=self.products.get(&key){id}else{
                // Forgetting cache entries only loses proofs. No atom ID is
                // recycled, and all live expressions keep their old meaning.
                if self.products.len()>=product_cap() {self.products.clear();}
                let id=self.fresh().atoms[0];self.products.insert(key,id);id
            };
            self.xor(&linear,&Affine{constant:false,atoms:vec![id]})
        }
    }

    fn ccx_rewrite(condition: &Affine, a: &Affine, b: &Affine, op: &Op) -> Rewrite {
        if condition.is_zero() || a.is_zero() || b.is_zero() || a.complements(b) {
            Rewrite::Drop
        } else if a.is_one() && b.is_one() {
            Rewrite::X
        } else if a.is_one() {
            Rewrite::Cx(op.q_control2)
        } else if b.is_one() || a == b {
            Rewrite::Cx(op.q_control1)
        } else {
            Rewrite::Keep
        }
    }

    pub(super) fn step(&mut self, op: &Op) -> Rewrite {
        if op.kind == OperationType::PushCondition {
            self.condition_stack.push(self.base_condition.clone());
            // Snapshot the current value, not a reference to the bit slot.
            self.base_condition = self.and(
                &self.base_condition.clone(),
                &self.bits[op.c_condition.0 as usize].clone(),
            );
            return Rewrite::Keep;
        }
        if op.kind == OperationType::PopCondition {
            if let Some(saved) = self.condition_stack.pop() {
                self.base_condition = saved;
            }
            return Rewrite::Keep;
        }

        let mut condition = self.base_condition.clone();
        if op.c_condition != NO_BIT {
            condition = self.and(&condition, &self.bits[op.c_condition.0 as usize].clone());
        }

        match op.kind {
            OperationType::CCX => {
                let a = self.qubits[op.q_control1.0 as usize].clone();
                let b = self.qubits[op.q_control2.0 as usize].clone();
                let mut rewrite = Self::ccx_rewrite(&condition, &a, &b, op);
                let product = self.and(&a, &b);
                let toggle = self.and(&condition, &product);
                if condition != Affine::constant(true) {
                    if toggle.is_zero() {rewrite=Rewrite::Drop;}
                    else if toggle == condition {rewrite=Rewrite::X;}
                    else if toggle == self.and(&condition,&a) {rewrite=Rewrite::Cx(op.q_control1);}
                    else if toggle == self.and(&condition,&b) {rewrite=Rewrite::Cx(op.q_control2);}
                }
                let target = op.q_target.0 as usize;
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &toggle);
                return rewrite;
            }
            OperationType::CX => {
                let target = op.q_target.0 as usize;
                let toggle = self.and(&condition, &self.qubits[op.q_control1.0 as usize].clone());
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &toggle);
            }
            OperationType::X => {
                let target = op.q_target.0 as usize;
                self.qubits[target] = self.xor(&self.qubits[target].clone(), &condition);
            }
            OperationType::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                let difference = self.xor(&self.qubits[a].clone(), &self.qubits[b].clone());
                let toggle = self.and(&condition, &difference);
                // Both destinations share this same actual conditional delta.
                let left = self.xor(&self.qubits[a].clone(), &toggle);
                let right = self.xor(&self.qubits[b].clone(), &toggle);
                self.qubits[a] = left;
                self.qubits[b] = right;
            }
            OperationType::Hmr => {
                let target = op.q_target.0 as usize;
                let bit = op.c_target.0 as usize;
                let outcome = self.fresh();
                let difference = self.xor(&self.bits[bit].clone(), &outcome);
                let toggle = self.and(&condition, &difference);
                self.bits[bit] = self.xor(&self.bits[bit].clone(), &toggle);
                self.qubits[target] =
                    self.and(&self.qubits[target].clone(), &condition.complement());
            }
            OperationType::R => {
                let target = op.q_target.0 as usize;
                self.qubits[target] =
                    self.and(&self.qubits[target].clone(), &condition.complement());
            }
            OperationType::BitInvert => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self.xor(&self.bits[bit].clone(), &condition);
            }
            OperationType::BitStore0 => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self.and(&self.bits[bit].clone(), &condition.complement());
            }
            OperationType::BitStore1 => {
                let bit = op.c_target.0 as usize;
                self.bits[bit] = self
                    .and(&self.bits[bit].complement(), &condition.complement())
                    .complement();
            }
            // Phase gates do not alter basis support. Preserve them, resets,
            // classical operations and annotations verbatim in the output.
            OperationType::Z
            | OperationType::CZ
            | OperationType::CCZ
            | OperationType::Neg
            | OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {}
            OperationType::PushCondition | OperationType::PopCondition => unreachable!(),
        }
        Rewrite::Keep
    }
}

impl Support {
    fn retain_large(&mut self,constant:bool,atoms:Vec<u64>)->Affine{
        if self.large_xors.len()>=50000{self.large_xors.clear();}
        let id=if let Some(&id)=self.large_xors.get(&atoms){id}else{let id=self.fresh().atoms[0];self.large_xors.insert(atoms,id);id};
        Affine{constant,atoms:vec![id]}
    }
}

/// Derive one pass of exact CCX support identities from this stream's ABI and
/// operations. No saved operation indices, nonce assumptions or legacy passes.
pub(crate) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let mut state = Support::new(&ops);
    let mut result = Vec::with_capacity(ops.len());
    let(mut dropped,mut linear,mut depth,mut proxy)=(0,0,0i32,0.0);
    for op in ops {
        if op.kind==OperationType::PushCondition{depth+=1;}
        if op.kind==OperationType::PopCondition{depth-=1;}
        let r=state.step(&op);
        if op.kind==OperationType::CCX {match r {Rewrite::Drop=>{dropped+=1;proxy+=2f64.powi(-depth-i32::from(op.c_condition!=NO_BIT));},Rewrite::X|Rewrite::Cx(_)=>{linear+=1;proxy+=2f64.powi(-depth-i32::from(op.c_condition!=NO_BIT));},_=>{}}}
        r.emit(op, &mut result);
    }
    println!("ANF_SIMPLIFY dropped={dropped} linear={linear} structural_proxy={proxy}");
    result
}


/// Exact CCX-to-CX witnesses. No new measurement, reset, or phase gate.
pub(crate) fn witnesses(ops:Vec<Op>)->Vec<Op>{
    use std::collections::{HashMap,BTreeSet};
    let mut state=Support::new(&ops);
    let mut index:HashMap<Affine,BTreeSet<usize>>=HashMap::new();
    for (q,v) in state.qubits.iter().enumerate(){index.entry(v.clone()).or_default().insert(q);}
    let(mut self_n,mut witness_n,mut self_t,mut witness_t,mut depth)=(0,0,0.0,0.0,0i32);
    let mut examples=Vec::new();
    let mut out=Vec::with_capacity(ops.len());
    for (at,op) in ops.iter().enumerate(){
        let mut replacement=None;
        if op.kind==OperationType::PushCondition{depth+=1;}
        if op.kind==OperationType::PopCondition{depth-=1;}
        if op.kind==OperationType::CCX{
            let a=state.qubits[op.q_control1.0 as usize].clone();
            let b=state.qubits[op.q_control2.0 as usize].clone();
            let product=state.and(&a,&b);
            let target=op.q_target.0 as usize;
            if !product.is_zero() && !product.is_one(){
                let weight=2f64.powi(-depth-i32::from(op.c_condition!=NO_BIT));
                let self_hit=state.qubits[target]==product;
                let witness=index.get(&product).and_then(|s|s.iter().copied().find(|&q|q!=target));
                if self_hit{self_n+=1;self_t+=weight;}
                if witness.is_some(){witness_n+=1;witness_t+=weight;replacement=witness;}
                if examples.len()<64 && (self_hit||witness.is_some()){
                    examples.push(format!("{{\"op\":{at},\"target\":{target},\"self_uncompute\":{self_hit},\"witness\":{}}}",witness.map_or("null".to_string(),|q|q.to_string())));
                }
            }
        }
        let changed:Vec<usize>=match op.kind{
            OperationType::CCX|OperationType::CX|OperationType::X|OperationType::R|OperationType::Hmr=>vec![op.q_target.0 as usize],
            OperationType::Swap=>vec![op.q_control1.0 as usize,op.q_target.0 as usize],_=>vec![]};
        for &q in &changed{let key=state.qubits[q].clone();let set=index.get_mut(&key).unwrap();assert!(set.remove(&q));if set.is_empty(){index.remove(&key);}}
        state.step(op);
        for &q in &changed{index.entry(state.qubits[q].clone()).or_default().insert(q);}
        if let Some(q)=replacement{
            assert_ne!(q,op.q_target.0 as usize);
            let mut r=Op::empty();r.kind=OperationType::CX;r.q_control1=QubitId(q as u64);r.q_target=op.q_target;r.c_condition=op.c_condition;
            r.validate();out.push(r);
        }else{out.push(*op);}
    }
    println!("I25_WITNESSES {{\"self_uncompute_native\":{self_n},\"self_uncompute_expected_T\":{self_t},\"witness_native\":{witness_n},\"witness_expected_T\":{witness_t},\"examples\":[{}]}}",examples.join(","));
    out
}

impl Support {
    pub(crate) fn cache_zeros(&self)->Vec<usize> {
        self.qubits.iter().enumerate().filter_map(|(q,v)|v.is_zero().then_some(q)).collect()
    }
    pub(crate) fn cache_product(&mut self,op:&Op)->(bool,Vec<u64>) {
        let a=self.qubits[op.q_control1.0 as usize].clone();
        let b=self.qubits[op.q_control2.0 as usize].clone();
        let p=self.and(&a,&b);(p.constant,p.atoms)
    }
}

#[cfg(test)]
mod anf_tests {
    use super::*;
    use quantum_ecc::sim::Simulator;
    struct Word(u64);
    impl sha3::digest::XofReader for Word {fn read(&mut self,out:&mut[u8]){out.copy_from_slice(&self.0.to_le_bytes());}}
    fn op(kind:OperationType,a:u64,b:u64,t:u64)->Op {let mut o=Op::empty();o.kind=kind;o.q_control1=QubitId(a);o.q_control2=QubitId(b);o.q_target=QubitId(t);o}
    #[test]
    fn oversized_xor_interning_preserves_complements_and_distinctions(){
        let mut s=Support::new(&[]);let mut atoms=vec![];
        for _ in 0..atom_cap()+1{atoms.push(s.fresh().atoms[0]);}
        let a=Affine{constant:false,atoms:atoms.clone()};let ca=a.complement();
        let x=s.xor(&a,&Affine::constant(false));let y=s.xor(&a,&Affine::constant(false));
        let cy=s.xor(&ca,&Affine::constant(false));
        assert!(x==y);assert!(x.complements(&cy));
        atoms.push(s.fresh().atoms[0]);let b=Affine{constant:false,atoms};
        let z=s.xor(&b,&Affine::constant(false));assert!(x!=z);assert!(!x.complements(&z));
    }
    #[test]
    fn distributive_witness_all_boolean_inputs_and_dirty_phase(){
        let z=u64::MAX;let mut p=vec![];
        let mut r=Op::empty();r.kind=OperationType::Register;r.r_target=crate::circuit::RegisterId(0);p.push(r);
        for q in 0..3 {let mut o=Op::empty();o.kind=OperationType::AppendToRegister;o.r_target=r.r_target;o.q_target=QubitId(q);p.push(o);}
        p.extend([
            op(OperationType::CX,0,z,3),op(OperationType::CX,1,z,3),
            op(OperationType::CCX,0,2,4),op(OperationType::CCX,1,2,5),
            op(OperationType::CX,5,z,4),op(OperationType::CCX,3,2,6),
        ]);
        let q=witnesses(simplify(p.clone()));
        assert_eq!(p.iter().filter(|o|o.kind==OperationType::CCX).count()-q.iter().filter(|o|o.kind==OperationType::CCX).count(),1);
        for input in 0..8 {for phase in [0,u64::MAX,0xa5a5a5a5a5a5a5a5] {
            let mut xa=Word(0);let mut xb=Word(0);
            let mut a=Simulator::new(7,0,&mut xa);let mut b=Simulator::new(7,0,&mut xb);
            for i in 0..3 {a.qubits[i]=if input>>i&1==1{u64::MAX}else{0};}b.qubits=a.qubits.clone();a.phase=phase;b.phase=phase;
            a.apply_iter(p.iter());b.apply_iter(q.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);
        }}
    }
}
