//! Exact late diagonal-phase folding. No sampled invariants or nonce changes.
//! Pending phases are GF(2) monomials in CURRENT wire values. X conjugation
//! substitutes q <- q XOR guard; incompatible classical products flush.
//! Each buffered phase remains inside one unchanged frozen stack scope.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::{BTreeSet, HashMap};
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Term { condition: u64, wires: Vec<u64> }
#[derive(Default)]
struct Pending { terms: BTreeSet<Term>, by_wire: HashMap<u64, BTreeSet<Term>> }
impl Pending {
    fn remove(&mut self, t: &Term) {
        if self.terms.remove(t) {
            for q in &t.wires { if let Some(v)=self.by_wire.get_mut(q) {v.remove(t);} }
        }
    }
    fn toggle(&mut self, t: Term) {
        if self.terms.contains(&t) {self.remove(&t);} else {
            for q in &t.wires {self.by_wire.entry(*q).or_default().insert(t.clone());}
            self.terms.insert(t);
        }
    }
    fn emit(t: Term, out: &mut Vec<Op>) {
        let mut o=Op::empty(); o.c_condition=BitId(t.condition);
        match t.wires.as_slice() {
            []=>o.kind=K::Neg,
            [a]=>{o.kind=K::Z;o.q_target=QubitId(*a);},
            [a,b]=>{o.kind=K::CZ;o.q_control1=QubitId(*a);o.q_target=QubitId(*b);},
            [a,b,c]=>{o.kind=K::CCZ;o.q_control2=QubitId(*a);o.q_control1=QubitId(*b);o.q_target=QubitId(*c);},
            _=>unreachable!(),
        }
        o.validate(); out.push(o);
    }
    fn flush_wire(&mut self,q:QubitId,out:&mut Vec<Op>) {
        if q==NO_QUBIT{return;}
        let affected=self.by_wire.get(&q.0).cloned().unwrap_or_default();
        for t in affected {self.remove(&t);Self::emit(t,out);}
    }
    fn flush(&mut self,out:&mut Vec<Op>) {
        for t in std::mem::take(&mut self.terms) {Self::emit(t,out);}
        self.by_wire.clear();
    }
    fn conjugate_x(&mut self,q:u64,condition:u64,out:&mut Vec<Op>) {
        let affected=self.by_wire.get(&q).cloned().unwrap_or_default();
        // f(q XOR c) = f(q) XOR c*f_without_q. We only represent
        // zero or one classical factor; unequal factors are full barriers.
        for mut t in affected {
            if condition!=NO_BIT.0 && t.condition!=NO_BIT.0 && condition!=t.condition {
                self.remove(&t);Self::emit(t,out);continue;
            }
            if t.condition==NO_BIT.0 {t.condition=condition;}
            t.wires.retain(|x|*x!=q);self.toggle(t);
        }
    }
}
pub fn run(ops:Vec<Op>)->Vec<Op> {
    let before=ops.iter().filter(|o|o.kind==K::CCZ).count();
    let mut pending=Pending::default();let mut out=Vec::with_capacity(ops.len());let mut depth=0usize;
    for o in ops {
        if o.kind==K::PushCondition {pending.flush(&mut out);depth+=1;out.push(o);continue;}
        if o.kind==K::PopCondition {pending.flush(&mut out);depth=depth.checked_sub(1).expect("unbalanced condition stack");out.push(o);continue;}
        match o.kind {
            K::Neg|K::Z|K::CZ|K::CCZ=>{
                let mut wires=match o.kind {K::Neg=>vec![],K::Z=>vec![o.q_target.0],K::CZ=>vec![o.q_control1.0,o.q_target.0],K::CCZ=>vec![o.q_control2.0,o.q_control1.0,o.q_target.0],_=>unreachable!()};
                wires.sort_unstable();wires.dedup();pending.toggle(Term{condition:o.c_condition.0,wires});
            },
            K::X=>{pending.conjugate_x(o.q_target.0,o.c_condition.0,&mut out);out.push(o);},
            K::CX|K::CCX|K::R=>{pending.flush_wire(o.q_target,&mut out);out.push(o);},
            K::Swap=>{pending.flush_wire(o.q_control1,&mut out);pending.flush_wire(o.q_target,&mut out);out.push(o);},
            // Classical writes, measurement outcomes, metadata and unknown
            // operations are conservative full barriers.
            _=>{pending.flush(&mut out);out.push(o);},
        }
        // Bound scratch space; flushing only limits optimization opportunity.
        if pending.terms.len()>4096 {pending.flush(&mut out);}
    }
    pending.flush(&mut out);assert_eq!(depth,0);
    let after=out.iter().filter(|o|o.kind==K::CCZ).count();assert!(after<=before);
    eprintln!("late_phase: CCZ {before} -> {after}, saved {}",before-after);
    out
}
