//! Exact Boolean tables over at most nine immutable value atoms.
//! Tables retain only essential variables. An unsupported union of supports
//! becomes one fresh atom for the WHOLE result, including any constant term.
//! Atom functions can be correlated; universal Boolean identities remain valid.

use super::affine_simplify::{Rewrite, Support as AffineSupport};
use super::quadratic_simplify::Support as QuadraticSupport;
use crate::circuit::{analyze_ops, Op, OperationType, QubitOrBit, NO_BIT};

const SUPPORT_CAP: usize = 9;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Truth {
    // Sorted immutable atom IDs. Bit j of a table row assigns atoms[j].
    atoms: Vec<u64>,
    table: Table,
}

include!("table.rs");

struct Support {
    qubits: Vec<Truth>,
    bits: Vec<Truth>,
    base_condition: Truth,
    condition_stack: Vec<Truth>,
    next_atom: u64,
}

impl Support {
    fn new(ops: &[Op]) -> Self {
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
            qubits: vec![Truth::constant(false); nq as usize],
            bits: vec![Truth::constant(false); nb as usize],
            base_condition: Truth::constant(true),
            condition_stack: Vec::new(),
            next_atom: 0,
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

    fn fresh(&mut self) -> Truth {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("truth atom identifier overflow");
        Truth {
            atoms: vec![id],
            table: Table::low(2),
        }
    }

    fn combine(&mut self, a: &Truth, b: &Truth, is_and: bool) -> Truth {
        let mut atoms = a.atoms.clone();
        atoms.extend(&b.atoms);
        atoms.sort_unstable();
        atoms.dedup();
        if atoms.len() > support_cap() {
            // Do not retain a partial table or constant. Even two identical
            // unsupported computations get distinct atoms unless copied.
            return self.fresh();
        }
        let positions = |value: &Truth| {
            value
                .atoms
                .iter()
                .map(|id| atoms.binary_search(id).unwrap())
                .collect::<Vec<_>>()
        };
        let a_positions = positions(a);
        let b_positions = positions(b);
        let mut table = Table::low(0);
        for row in 0..1usize << atoms.len() {
            let left = a.value_in_union(&a_positions, row);
            let right = b.value_in_union(&b_positions, row);
            let value = if is_and { left & right } else { left ^ right };
            table.set(row, value);
        }
        Truth::canonical(atoms, table)
    }

    fn xor(&mut self, a: &Truth, b: &Truth) -> Truth {
        if a == b {
            return Truth::constant(false);
        }
        if a.is_zero() {
            return b.clone();
        }
        if b.is_zero() {
            return a.clone();
        }
        if a.is_one() {
            return b.complement();
        }
        if b.is_one() {
            return a.complement();
        }
        self.combine(a, b, false)
    }

    fn and(&mut self, a: &Truth, b: &Truth) -> Truth {
        if a.is_zero() || b.is_zero() || a.complements(b) {
            return Truth::constant(false);
        }
        if a.is_one() {
            return b.clone();
        }
        if b.is_one() || a == b {
            return a.clone();
        }
        self.combine(a, b, true)
    }

    fn ccx_rewrite(condition: &Truth, a: &Truth, b: &Truth, op: &Op) -> Rewrite {
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

    fn step(&mut self, op: &Op) -> Rewrite {
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
                let product = self.and(&a, &b);
                let toggle = self.and(&condition, &product);
                // Equality is of whole immutable Boolean functions. Failed
                // Compare the actual conditional toggle, retaining the exact
                // original classical condition and stack in every replacement.
                let rewrite = if toggle.is_zero() {
                    Rewrite::Drop
                } else if toggle == condition {
                    Rewrite::X
                } else if toggle == self.and(&condition, &a) {
                    Rewrite::Cx(op.q_control1)
                } else if toggle == self.and(&condition, &b) {
                    Rewrite::Cx(op.q_control2)
                } else {
                    Self::ccx_rewrite(&condition, &a, &b, op)
                };
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
use std::collections::{HashMap,BTreeSet};
struct Index{values:HashMap<Truth,BTreeSet<usize>>, by_atom:HashMap<u64,BTreeSet<usize>>, eligible:Vec<bool>}
impl Index{
 fn new(st:&Support)->Self{let mut x=Self{values:HashMap::new(),by_atom:HashMap::new(),eligible:vec![true;st.qubits.len()]};for q in 0..st.qubits.len(){x.insert(st,q);}x}
 fn insert(&mut self,st:&Support,q:usize){if !self.eligible[q]{return;}let v=&st.qubits[q];self.values.entry(v.clone()).or_default().insert(q);for a in &v.atoms{self.by_atom.entry(*a).or_default().insert(q);}}
 fn remove(&mut self,st:&Support,q:usize){let v=&st.qubits[q];if let Some(qs)=self.values.get_mut(v){qs.remove(&q);if qs.is_empty(){self.values.remove(v);}}for a in &v.atoms{if let Some(qs)=self.by_atom.get_mut(a){qs.remove(&q);if qs.is_empty(){self.by_atom.remove(a);}}}}
 fn lookup(&self,st:&mut Support,o:&Op)->Option<(Vec<usize>,bool)>{
  let a=st.qubits[o.q_control1.0 as usize].clone();let b=st.qubits[o.q_control2.0 as usize].clone();
  let mut atoms=a.atoms.clone();atoms.extend(&b.atoms);atoms.sort_unstable();atoms.dedup();if atoms.len()>SUPPORT_CAP{return None;}
  let product=st.and(&a,&b);let t=o.q_target.0 as usize;
  if product.is_zero(){return Some((vec![],false));}if product.is_one(){return Some((vec![],true));}
  for (v,neg) in [(product.clone(),false),(product.complement(),true)]{if let Some(qs)=self.values.get(&v){if let Some(&q)=qs.iter().find(|&&q|q!=t){return Some((vec![q],neg));}}}
  let candidates:BTreeSet<usize>=product.atoms.iter().filter_map(|a|self.by_atom.get(a)).flat_map(|qs|qs.iter().copied()).filter(|&q|q!=t).collect();
  for q in candidates{
   let v=st.qubits[q].clone();let mut atoms=product.atoms.clone();atoms.extend(&v.atoms);atoms.sort_unstable();atoms.dedup();if atoms.len()>SUPPORT_CAP{continue;}
   let rest=st.xor(&product,&v);
   for (r,neg)in[(rest.clone(),false),(rest.complement(),true)]{if let Some(qs)=self.values.get(&r){if let Some(&q2)=qs.iter().find(|&&q2|q2!=t&&q2!=q){return Some((vec![q,q2],neg));}}}
  }
  let candidates:BTreeSet<usize>=product.atoms.iter().filter_map(|a|self.by_atom.get(a)).flat_map(|qs|qs.iter().copied()).filter(|&q|q!=t).collect();
  let lead=|x:&Table|{x.0.iter().enumerate().rev().find(|(_,v)|**v!=0).map(|(i,v)|i*64+63-v.leading_zeros() as usize)};
  let mut basis:Vec<Option<(Table,BTreeSet<usize>)>>=vec![None;512];
  for q in std::iter::once(usize::MAX).chain(candidates){
   let v=if q==usize::MAX{Truth::constant(true)}else{st.qubits[q].clone()};
   if v.atoms.iter().any(|a|product.atoms.binary_search(a).is_err()){continue;}
   let positions:Vec<usize>=v.atoms.iter().map(|a|product.atoms.binary_search(a).unwrap()).collect();
   let mut bits=Table::low(0);for row in 0..1usize<<product.atoms.len(){bits.set(row,v.value_in_union(&positions,row));}
   let mut combo=BTreeSet::from([q]);
   while let Some(l)=lead(&bits){if let Some((b,c))=&basis[l]{bits=bits.xor(*b);combo=combo.symmetric_difference(c).copied().collect();}else{basis[l]=Some((bits,combo));break;}}
  }
  let mut bits=product.table;let mut combo=BTreeSet::new();
  while let Some(l)=lead(&bits){if let Some((b,c))=&basis[l]{bits=bits.xor(*b);combo=combo.symmetric_difference(c).copied().collect();}else{return None;}}
  let neg=combo.remove(&usize::MAX);if combo.len()<=8{return Some((combo.into_iter().collect(),neg));}None
 }
}
fn changes(o:&Op)->Vec<usize>{use OperationType::*;match o.kind{X|CX|CCX|R|Hmr=>vec![o.q_target.0 as usize],Swap=>vec![o.q_control1.0 as usize,o.q_target.0 as usize],_=>vec![]}}
pub fn simplify(ops:Vec<Op>)->Vec<Op>{
 let mut st=Support::new(&ops);let mut idx=Index::new(&st);let mut out=Vec::with_capacity(ops.len());let mut hits=[0;9];
 for(i,o)in ops.into_iter().enumerate(){
  let hit=if o.kind==OperationType::CCX{idx.lookup(&mut st,&o)}else{None};let changed=changes(&o);for &q in &changed{idx.remove(&st,q);}
  if let Some((qs,neg))=hit{hits[qs.len()]+=1;
   if neg{let mut x=Op::empty();x.kind=OperationType::X;x.q_target=o.q_target;x.c_condition=o.c_condition;x.validate();st.step(&x);out.push(x);}
   for q in &qs{let mut cx=Op::empty();cx.kind=OperationType::CX;cx.q_target=o.q_target;cx.q_control1=crate::circuit::QubitId(*q as u64);cx.c_condition=o.c_condition;cx.validate();st.step(&cx);out.push(cx);}
   eprintln!("WIDE_SPAN_HIT op={i} qs={qs:?} neg={neg} original={o:?}");
  }else{st.step(&o);out.push(o);}
  for &q in &changed{idx.insert(&st,q);}
 }
 eprintln!("WIDE_SPAN hits={hits:?}");out
}
