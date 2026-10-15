//! Exact Boolean-ring phase audit for fixed bit-packed basis inputs.
//!
//! Independent indeterminates denote EACH R/HMR outcome, never mutable BitIds.
//! u64 coefficients hold 64 separate input lanes. Zero ANF proves zero phase
//! for all measurement choices on those inputs. Overflow is inconclusive.
use crate::circuit::{analyze_ops, Op, OperationType as K, NO_BIT};
use std::collections::BTreeMap;

const TERM_CAP: usize = 8192;
const MULTIPLY_WORK_CAP: usize = 1_000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Poly(BTreeMap<Vec<u32>, u64>);

fn union(a: &[u32], b: &[u32]) -> Vec<u32> {
    let (mut i, mut j, mut out) = (0, 0, Vec::with_capacity(a.len() + b.len()));
    while i < a.len() || j < b.len() {
        if j == b.len() || (i < a.len() && a[i] < b[j]) { out.push(a[i]); i += 1; }
        else if i == a.len() || b[j] < a[i] { out.push(b[j]); j += 1; }
        else { out.push(a[i]); i += 1; j += 1; }
    }
    out
}

impl Poly {
    fn constant(v: u64) -> Self {
        let mut terms = BTreeMap::new();
        if v != 0 { terms.insert(Vec::new(), v); }
        Self(terms)
    }
    fn variable(id: u32) -> Self { Self(BTreeMap::from([(vec![id], u64::MAX)])) }
    fn scalar(&self) -> Option<u64> {
        if self.0.is_empty() { Some(0) }
        else if self.0.len() == 1 { self.0.get(&Vec::new()).copied() }
        else { None }
    }
    fn accumulate(&mut self, monomial: Vec<u32>, value: u64) {
        if value == 0 { return; }
        let entry = self.0.entry(monomial.clone()).or_insert(0);
        *entry ^= value;
        if *entry == 0 { self.0.remove(&monomial); }
    }
    fn xor(&self, other: &Self) -> Result<Self, String> {
        let mut result = self.clone();
        for (monomial, value) in &other.0 { result.accumulate(monomial.clone(), *value); }
        if result.0.len() > TERM_CAP { return Err("inconclusive: XOR term cap".into()); }
        Ok(result)
    }
    fn and(&self, other: &Self) -> Result<Self, String> {
        if let Some(mask) = self.scalar() { return Ok(other.masked(mask)); }
        if let Some(mask) = other.scalar() { return Ok(self.masked(mask)); }
        if self.0.len().saturating_mul(other.0.len()) > MULTIPLY_WORK_CAP {
            return Err("inconclusive: multiplication work cap".into());
        }
        let mut result = Self::constant(0);
        for (a, av) in &self.0 { for (b, bv) in &other.0 {
            result.accumulate(union(a, b), av & bv);
            if result.0.len() > TERM_CAP { return Err("inconclusive: AND term cap".into()); }
        }}
        Ok(result)
    }
    fn masked(&self, mask: u64) -> Self {
        Self(self.0.iter().filter_map(|(m, v)| ((*v & mask) != 0).then(|| (m.clone(), *v & mask))).collect())
    }
    fn not(&self) -> Result<Self, String> { self.xor(&Self::constant(u64::MAX)) }
}

#[derive(Debug)]
pub struct Audit {
    pub qubits: Vec<u64>,
    pub measurements: u64,
    pub maximum_phase_terms: usize,
    pub maximum_quantum_terms: usize,
}

/// Classical slots start at the supplied constants, with remaining scratch 0.
/// Final quantum values must be independent of measurements. Classical scratch
/// may retain outcomes. This is a finite INPUT-domain proof, not a score.
pub fn audit(ops: &[Op], input: &[u64], initial_bits: &[u64]) -> Result<Audit, String> {
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    if input.len() < nq as usize { return Err("input shorter than quantum allocation".into()); }
    let mut q: Vec<_> = input.iter().map(|v| Poly::constant(*v)).collect();
    let mut bits = vec![Poly::constant(0); (nb as usize).max(initial_bits.len())];
    for (bit, value) in initial_bits.iter().enumerate() { bits[bit] = Poly::constant(*value); }
    let mut phase = Poly::constant(0);
    let mut base = Poly::constant(u64::MAX);
    let mut stack = Vec::new();
    let mut next_measurement = 0u32;
    let (mut max_phase, mut max_quantum) = (0, 1);
    for (index, op) in ops.iter().enumerate() {
        let condition = if op.c_condition == NO_BIT { base.clone() }
            else { base.and(&bits[op.c_condition.0 as usize])? };
        let (a, b, t, bit) = (op.q_control1.0 as usize, op.q_control2.0 as usize,
                             op.q_target.0 as usize, op.c_target.0 as usize);
        match op.kind {
            K::PushCondition => { stack.push(base); base = condition; }
            K::PopCondition => { base = stack.pop().ok_or_else(|| format!("unbalanced pop at {index}"))?; }
            K::X => { q[t] = q[t].xor(&condition)?; }
            K::CX => { q[t] = q[t].xor(&condition.and(&q[a])?)?; }
            K::CCX => { q[t] = q[t].xor(&condition.and(&q[a].and(&q[b])?)?)?; }
            K::Swap => {
                let delta = condition.and(&q[a].xor(&q[t])?)?;
                q[a] = q[a].xor(&delta)?; q[t] = q[t].xor(&delta)?;
            }
            K::R | K::Hmr => {
                let m = Poly::variable(next_measurement);
                next_measurement = next_measurement.checked_add(1).ok_or("measurement id overflow")?;
                phase = phase.xor(&condition.and(&q[t].and(&m)?)?)?;
                if op.kind == K::Hmr {
                    bits[bit] = bits[bit].xor(&condition.and(&bits[bit].xor(&m)?)?)?;
                }
                q[t] = q[t].and(&condition.not()?)?;
            }
            K::BitInvert => { bits[bit] = bits[bit].xor(&condition)?; }
            K::BitStore0 => { bits[bit] = bits[bit].and(&condition.not()?)?; }
            K::BitStore1 => { bits[bit] = bits[bit].xor(&condition.and(&bits[bit].not()?)?)?; }
            K::Neg => { phase = phase.xor(&condition)?; }
            K::Z => { phase = phase.xor(&condition.and(&q[t])?)?; }
            K::CZ => { phase = phase.xor(&condition.and(&q[a].and(&q[t])?)?)?; }
            K::CCZ => { phase = phase.xor(&condition.and(&q[a].and(&q[b].and(&q[t])?)?)?)?; }
            K::Register | K::AppendToRegister | K::DebugPrint => {}
        }
        max_phase = max_phase.max(phase.0.len());
        match op.kind {
            K::X | K::CX | K::CCX | K::R | K::Hmr => { max_quantum = max_quantum.max(q[t].0.len()); }
            K::Swap => { max_quantum = max_quantum.max(q[t].0.len()).max(q[a].0.len()); }
            _ => {}
        }
    }
    if !stack.is_empty() { return Err("unclosed condition stack".into()); }
    if !phase.0.is_empty() {
        return Err(format!("nonzero phase polynomial: {} terms; first {:?}", phase.0.len(), phase.0.first_key_value()));
    }
    let mut output = Vec::with_capacity(q.len());
    for (slot, value) in q.iter().enumerate() {
        output.push(value.scalar().ok_or_else(|| format!("measurement-dependent final quantum slot {slot}"))?);
    }
    Ok(Audit { qubits: output, measurements: next_measurement as u64,
               maximum_phase_terms: max_phase, maximum_quantum_terms: max_quantum })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId, QubitId};
    fn native(ops: &[Op], input: &[u64], words: &[u64]) -> (Vec<u64>, u64) {
        struct Reader<'a> { words: &'a [u64], at: usize }
        impl sha3::digest::XofReader for Reader<'_> {
            fn read(&mut self, bytes: &mut [u8]) {
                assert_eq!(bytes.len(),8); bytes.copy_from_slice(&self.words[self.at].to_le_bytes()); self.at+=1;
            }
        }
        let (_,nb,_,_)=analyze_ops(ops.iter());let mut reader=Reader{words,at:0};
        let mut sim=quantum_ecc::sim::Simulator::new(input.len(),nb as usize,&mut reader);
        sim.qubits=input.to_vec();sim.apply_iter(ops.iter());(sim.qubits,sim.phase)
    }
    fn gate(k: K, a: Option<u64>, b: Option<u64>, t: Option<u64>, bit: Option<u64>, condition: Option<u64>) -> Op {
        let mut op = Op::empty(); op.kind = k;
        if let Some(a) = a { op.q_control1 = QubitId(a); }
        if let Some(b) = b { op.q_control2 = QubitId(b); }
        if let Some(t) = t { op.q_target = QubitId(t); }
        if let Some(bit) = bit { op.c_target = BitId(bit); }
        if let Some(c) = condition { op.c_condition = BitId(c); }
        op.validate(); op
    }
    #[test]
    fn snapshot_mutation_nested_push_and_phase_fault() {
        let mut ops = vec![
            gate(K::Hmr,None,None,Some(0),Some(0),None),
            gate(K::PushCondition,None,None,None,None,Some(0)),
            gate(K::BitInvert,None,None,None,Some(0),None),
            gate(K::BitStore1,None,None,None,Some(1),None),
            gate(K::PushCondition,None,None,None,None,Some(1)),
            gate(K::Z,None,None,Some(1),None,None),
            gate(K::PopCondition,None,None,None,None,None),
            gate(K::PopCondition,None,None,None,None,None),
        ];
        let mask=0x934ce2086ffa3145;let input=[mask,mask,!mask];
        let result=audit(&ops,&input,&[]).unwrap();assert_eq!(result.qubits,vec![0,mask,!mask]);assert_eq!(result.measurements,1);
        for m in [0,u64::MAX,0x682ab19376cdfe08] {let(q,phase)=native(&ops,&input,&[m]);assert_eq!(q,result.qubits);assert_eq!(phase,0);}
        ops[5].q_target=QubitId(2);
        assert!(audit(&ops,&input,&[]).unwrap_err().starts_with("nonzero phase polynomial"));
        assert_eq!(native(&ops,&input,&[u64::MAX]).1,u64::MAX);
    }
    #[test]
    fn conditional_hmr_boolean_idempotence_and_value_restoration() {
        let ops=vec![
            gate(K::Hmr,None,None,Some(0),Some(0),None),
            gate(K::PushCondition,None,None,None,None,Some(0)),
            gate(K::Hmr,None,None,Some(1),Some(1),None),
            gate(K::Z,None,None,Some(2),None,Some(1)),
            gate(K::CX,Some(2),None,Some(1),None,None),
            gate(K::PopCondition,None,None,None,None,None),
        ];
        let input=[0,0x123456789abcdef0,0x123456789abcdef0];
        let result=audit(&ops,&input,&[]).unwrap();assert_eq!(result.qubits,input);assert_eq!(result.measurements,2);
        assert!(result.maximum_quantum_terms>1);
        for m in [0,u64::MAX] {for n in [0,u64::MAX] {let(q,phase)=native(&ops,&input,&[m,n]);assert_eq!(q,input);assert_eq!(phase,0);}}
    }
    #[test]
    fn discarded_phase_only_block_is_detected() {
        let ops=vec![gate(K::Hmr,None,None,Some(0),Some(0),None),
            gate(K::PushCondition,None,None,None,None,Some(0)),
            gate(K::CCZ,Some(1),Some(2),Some(3),None,None),
            gate(K::PopCondition,None,None,None,None,None)];
        assert!(audit(&ops,&[0,u64::MAX,u64::MAX,u64::MAX],&[]).unwrap_err().starts_with("nonzero phase polynomial"));
        assert_eq!(native(&ops,&[0,u64::MAX,u64::MAX,u64::MAX],&[u64::MAX]).1,u64::MAX);
    }
    #[test]
    fn support_limit_is_inconclusive() {
        let many=Poly((0..TERM_CAP+1).map(|i|(vec![i as u32],1u64)).collect());
        assert_eq!(many.xor(&Poly::constant(0)).unwrap_err(),"inconclusive: XOR term cap");
    }
}
