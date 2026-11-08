//! Isolated audit data; the mechanically moved simulator is test-only.
use crate::circuit::{Op, OperationType, QubitId};

// Isolated component audit metadata. This never changes simulation semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum C162Relation {
    Clean,
    Product(QubitId, QubitId),
    // carry((t XOR flip) + source + incoming), low bits first.
    Carry { t: Vec<QubitId>, source: Vec<C162Expr>, incoming: QubitId, flip: C162Expr },
    Value(C162Expr),
    Unchecked,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum C162Expr {
    Zero, One, Wire(QubitId),
    Mux { a: Option<QubitId>, previous: Option<QubitId>, sigma: QubitId, sign: QubitId },
}
impl C162Expr {
    fn value(&self, q: &[u64]) -> u64 {
        let v = |id: QubitId| q[id.0 as usize];
        match self {
            Self::Zero => 0, Self::One => u64::MAX, Self::Wire(id) => v(*id),
            Self::Mux { a, previous, sigma, sign } => {
                let a = a.map_or(0, v); let previous = previous.map_or(0, v);
                a ^ (v(*sigma) & (a ^ previous)) ^ v(*sign)
            }
        }
    }
    fn ports(&self, out: &mut Vec<QubitId>) {
        match self {
            Self::Wire(q) => out.push(*q),
            Self::Mux { a, previous, sigma, sign } => {
                out.extend(*a); out.extend(*previous); out.extend([*sigma, *sign]);
            }
            _ => {}
        }
    }
}
impl C162Relation {
    fn expected(&self, q: &[u64]) -> Option<u64> {
        match self {
            Self::Clean => Some(0),
            Self::Product(a,b) => Some(q[a.0 as usize] & q[b.0 as usize]),
            Self::Value(e) => Some(e.value(q)),
            Self::Carry { t, source, incoming, flip } => {
                assert_eq!(t.len(),source.len());
                let mut carry=q[incoming.0 as usize]; let flip=flip.value(q);
                for (t,s) in t.iter().zip(source) {
                    let a=q[t.0 as usize]^flip; let b=s.value(q);
                    carry=(a&b)^((a^b)&carry);
                }
                Some(carry)
            }
            Self::Unchecked => None,
        }
    }
    fn ports(&self) -> Vec<QubitId> {
        let mut out=vec![];
        match self {
            Self::Product(a,b) => out.extend([*a,*b]),
            Self::Value(e) => e.ports(&mut out),
            Self::Carry {t,source,incoming,flip} => {
                out.extend(t); out.push(*incoming); flip.ports(&mut out);
                for e in source {e.ports(&mut out);}
            }
            _=>{}
        }
        out.sort(); out.dedup(); out
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct C162Audit {
    pub at: usize,
    pub family: &'static str,
    pub operation: Op,
    pub relation: C162Relation,
    // Exact final emitted correction, including nested conditions. Relative offsets
    // let a deliberately inserted mutant shift the whole recipe without rebinding it.
    pub correction: Vec<Op>,
}
pub fn c162_validate_shape(ops: &[Op], entries: &[C162Audit]) -> Result<(),String> {
    let mut previous=None;
    for e in entries {
        if previous.is_some_and(|p|p>=e.at) {return Err(format!("nonmonotonic audit index {}",e.at));}
        previous=Some(e.at);
        if ops.get(e.at)!=Some(&e.operation) {return Err(format!("operation shape at {}",e.at));}
        match &e.relation {
            C162Relation::Clean if e.operation.kind!=OperationType::CCX => return Err("AND_C kind".into()),
            C162Relation::Product(a,b) => {
                let expected=Op{kind:OperationType::CZ,q_control1:*a,q_target:*b,
                    c_condition:e.operation.c_target,..Op::empty()};
                if e.operation.kind!=OperationType::Hmr || e.correction!=vec![expected] {
                    return Err(format!("AND_U correction shape at {}",e.at));
                }
            }
            C162Relation::Clean => {},
            _ if e.operation.kind!=OperationType::Hmr => return Err("erase kind".into()),
            _=>{}
        }
        let end=e.at+1+e.correction.len();
        if ops.get(e.at+1..end)!=Some(e.correction.as_slice()) {return Err(format!("correction changed at {}",e.at));}
    }
    let recorded=entries.iter().filter(|e|e.operation.kind==OperationType::Hmr).count();
    if recorded!=ops.iter().filter(|o|o.kind==OperationType::Hmr).count() {return Err("unlabelled HMR".into());}
    Ok(())
}
#[derive(Clone, Debug)]
pub struct C162Witness {
    pub index:usize, pub family:&'static str, pub operation:Op,
    pub relation:C162Relation, pub correction:Vec<Op>,
    pub held:u64, pub expected:u64, pub control_words:Vec<(QubitId,u64)>,
    pub base_mask:u64, pub explicit_mask:u64, pub valid_mask:u64,
    pub residual:u64, pub executed_residual:u64,
    pub fixture_ids:Vec<(usize,String)>, pub direction:&'static str,
}
#[derive(Clone, Debug, Default)]
pub struct C162Counts {
    pub operations:usize, pub executed_lane_checks:u64, pub bad_operations:usize,
    pub bad_lanes:u64, pub bad_lane_mask:u64, pub unchecked_operations:usize,
}

#[cfg(test)]
pub(crate) mod simulator {
use super::{C162Audit, C162Relation, C162Counts, C162Witness};
use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT};
use ruint::aliases::U256;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SimStats {
    pub clifford_gates: u64,
    pub toffoli_gates: u64,
}



pub struct Simulator<'a, R: sha3::digest::XofReader> {
    pub phase: u64,
    pub c162_audit: Vec<C162Audit>,
    pub c162_checked: usize,
    pub c162_valid_mask: u64,
    pub c162_select_mask: u64,
    pub c162_fixture_ids: Vec<String>,
    pub c162_direction: &'static str,
    pub c162_counts: std::collections::BTreeMap<&'static str,C162Counts>,
    pub c162_bad: Vec<C162Witness>,
    pub c162_first_product: Option<(usize,u64)>,
    pub qubits: Vec<u64>,
    pub bits: Vec<u64>,
    pub num_qubits: usize,
    pub num_bits: usize,
    pub xof: &'a mut R,
    pub stats: SimStats,
}

impl<'a, R: sha3::digest::XofReader> Simulator<'a, R> {
    pub fn new(num_qubits: usize, num_bits: usize, xof: &'a mut R) -> Self {
        let qubits = vec![0; num_qubits];
        let bits = vec![0; num_bits];

        Self {
            phase: 0, c162_audit: Vec::new(), c162_checked: 0, c162_bad: Vec::new(),
            c162_valid_mask:u64::MAX, c162_select_mask:u64::MAX, c162_fixture_ids:vec![], c162_direction:"unspecified",
            c162_counts:Default::default(), c162_first_product:None,
            qubits,
            bits,
            num_qubits,
            num_bits,
            xof,
            stats: SimStats::default(),
        }
    }

    #[inline(always)]
    pub fn qubit(&self, id: QubitId) -> u64 {
        self.qubits[id.0 as usize]
    }

    #[inline(always)]
    pub fn qubit_mut(&mut self, id: QubitId) -> &mut u64 {
        &mut self.qubits[id.0 as usize]
    }

    #[inline(always)]
    pub fn bit(&self, id: BitId) -> u64 {
        self.bits[id.0 as usize]
    }

    #[inline(always)]
    pub fn bit_mut(&mut self, id: BitId) -> &mut u64 {
        &mut self.bits[id.0 as usize]
    }

    pub fn clear_for_shot(&mut self) {
        for e in &mut self.qubits {
            *e = 0;
        }
        for e in &mut self.bits {
            *e = 0;
        }
        self.phase = 0;
    }

    pub fn apply_iter<'b>(&mut self, ops: impl Iterator<Item = &'b Op>) {

        let mut condition_stack = Vec::new();
        let mut current_base_condition = u64::MAX;

        for (c162_i,op) in ops.enumerate() {
            let explicit = if op.c_condition==NO_BIT {u64::MAX} else {self.bit(op.c_condition)};
            let cond = current_base_condition & explicit;
            if let Some(e)=self.c162_audit.get(self.c162_checked) {
                assert!(e.at>=c162_i,"missed audit index");
                if e.at==c162_i {
                    assert_eq!(*op,e.operation,"final operation shape");
                    let executing=cond & self.c162_valid_mask;
                    let expected=e.relation.expected(&self.qubits);
                    let held=self.qubit(op.q_target);
                    let count=self.c162_counts.entry(e.family).or_default();
                    count.operations+=1;
                    if let Some(expected)=expected {
                        count.executed_lane_checks+=executing.count_ones() as u64;
                        let residual=held^expected; let bad=residual&executing;
                        if matches!(&e.relation,C162Relation::Product(..)) && executing&self.c162_select_mask!=0 && self.c162_first_product.is_none()
                            && !self.c162_audit.iter().take_while(|prior|prior.at<e.at)
                                .any(|prior|prior.at+prior.correction.len()>=e.at) {
                            self.c162_first_product=Some((e.at,executing&self.c162_select_mask));
                        }
                        if bad!=0 {
                            count.bad_operations+=1; count.bad_lanes+=bad.count_ones() as u64; count.bad_lane_mask|=bad;
                            if self.c162_bad.len()<16 {
                                self.c162_bad.push(C162Witness{index:e.at,family:e.family,operation:*op,
                                    relation:e.relation.clone(),correction:e.correction.clone(),held,expected,
                                    control_words:{let mut ports=e.relation.ports();
                                        for q in [op.q_control1,op.q_control2] {if q!=crate::circuit::NO_QUBIT {ports.push(q);}}
                                        ports.sort();ports.dedup();ports.iter().map(|q|(*q,self.qubits[q.0 as usize])).collect()},
                                    base_mask:current_base_condition,explicit_mask:explicit,valid_mask:self.c162_valid_mask,
                                    residual,executed_residual:bad,direction:self.c162_direction,
                                    fixture_ids:(0..64).filter(|i|bad&(1u64<<i)!=0)
                                        .map(|i|(i,self.c162_fixture_ids.get(i).cloned().unwrap_or_else(||format!("control_lane_{}",i)))).collect()});
                            }
                        }
                    } else {count.unchecked_operations+=1;}
                    self.c162_checked+=1;
                }
            }

            let executed_shots = cond.count_ones() as u64;

            match op.kind {
                OperationType::CCZ | OperationType::CCX => {
                    self.stats.toffoli_gates += executed_shots;
                }
                OperationType::CX
                | OperationType::CZ
                | OperationType::Swap
                | OperationType::R
                | OperationType::Hmr => {
                    self.stats.clifford_gates += executed_shots;
                }
                // Note: X and Z are not considered Clifford gates in the
                // stats because they can be tracked in the classical control system.
                // They don't need to cause something to happen on the quantum computer.
                _ => {}
            }

            match op.kind {
                OperationType::CCX => {
                    let v = cond & self.qubit(op.q_control1) & self.qubit(op.q_control2);
                    *self.qubit_mut(op.q_target) ^= v;
                }
                OperationType::CX => {
                    let v = cond & self.qubit(op.q_control1);
                    *self.qubit_mut(op.q_target) ^= v;
                }
                OperationType::Swap => {
                    let mut q_c1 = self.qubit(op.q_control1);
                    let mut q_t = self.qubit(op.q_target);
                    q_c1 ^= q_t;
                    q_t ^= cond & q_c1;
                    q_c1 ^= q_t;
                    *self.qubit_mut(op.q_control1) = q_c1;
                    *self.qubit_mut(op.q_target) = q_t;
                }
                OperationType::X => {
                    *self.qubit_mut(op.q_target) ^= cond;
                }
                OperationType::CCZ => {
                    let v = cond
                        & self.qubit(op.q_target)
                        & self.qubit(op.q_control1)
                        & self.qubit(op.q_control2);
                    self.phase ^= v;
                }
                OperationType::CZ => {
                    let v = cond & self.qubit(op.q_target) & self.qubit(op.q_control1);
                    self.phase ^= v;
                }
                OperationType::Z => {
                    let v = cond & self.qubit(op.q_target);
                    self.phase ^= v;
                }
                OperationType::Neg => {
                    self.phase ^= cond;
                }
                OperationType::Hmr => {
                    let mut buf = [0u8; 8];
                    self.xof.read(&mut buf);
                    let rng_val = u64::from_le_bytes(buf);
                    *self.bit_mut(op.c_target) &= !cond;
                    *self.bit_mut(op.c_target) ^= rng_val & cond;
                    self.phase ^= self.qubit(op.q_target) & rng_val & cond;
                    *self.qubit_mut(op.q_target) &= !cond;
                }
                OperationType::R => {
                    let mut buf = [0u8; 8];
                    self.xof.read(&mut buf);
                    let rng_val = u64::from_le_bytes(buf);
                    self.phase ^= self.qubit(op.q_target) & rng_val & cond;
                    *self.qubit_mut(op.q_target) &= !cond;
                }
                OperationType::BitInvert => {
                    *self.bit_mut(op.c_target) ^= cond;
                }
                OperationType::BitStore0 => {
                    *self.bit_mut(op.c_target) &= !cond;
                }
                OperationType::BitStore1 => {
                    *self.bit_mut(op.c_target) |= cond;
                }
                OperationType::AppendToRegister
                | OperationType::Register
                | OperationType::DebugPrint => {}
                OperationType::PushCondition => {
                    condition_stack.push(current_base_condition);
                    current_base_condition &= self.bit(op.c_condition);
                }
                OperationType::PopCondition => {
                    if let Some(val) = condition_stack.pop() {
                        current_base_condition = val;
                    }
                }
            }
        }

    }

    /// Writes an integer into the qubits/bits of a register.
    ///
    /// Args:
    ///     reg: The qubits and bits making up the register, in little endian order.
    ///         CAUTION: Writes are unchecked!
    ///             Only pass in bits and qubits consistent with num_bits and num_qubits!
    ///         Caution: if a qubit or bit appears multiple times, the write to the more
    ///             significant bit position will overwrite prior writes.
    ///     val: The value to write into the bits/qubits.
    ///     shot_idx: The simulator tracks 64 shots in parallel. This is which shot to write to.
    pub fn set_register(
        &mut self,
        reg: &[crate::circuit::QubitOrBit],
        val: U256,
        shot_idx: usize,
    ) {
        for (i, item) in reg.iter().enumerate() {
            let bit_val = val.bit(i);
            match item {
                crate::circuit::QubitOrBit::Qubit(id) => {
                    if bit_val {
                        *self.qubit_mut(*id) |= 1 << shot_idx;
                    } else {
                        *self.qubit_mut(*id) &= !(1 << shot_idx);
                    }
                }
                crate::circuit::QubitOrBit::Bit(id) => {
                    if bit_val {
                        *self.bit_mut(*id) |= 1 << shot_idx;
                    } else {
                        *self.bit_mut(*id) &= !(1 << shot_idx);
                    }
                }
            }
        }
    }

    /// Reads the qubits/bits of a register as an integer.
    ///
    /// Args:
    ///     reg: The qubits and bits making up the register, in little endian order.
    ///         CAUTION: Reads are unchecked!
    ///             Only pass in bits and qubits consistent with num_bits and num_qubits!
    ///     shot_idx: The simulator tracks 64 shots in parallel. This is which shot to read from.
    ///
    /// Returns:
    ///     The requested integer.
    pub fn get_register(
        &self,
        reg: &[crate::circuit::QubitOrBit],
        shot_idx: usize,
    ) -> U256 {
        let mut v = U256::ZERO;
        for (i, item) in reg.iter().enumerate() {
            let bit_val = match item {
                crate::circuit::QubitOrBit::Qubit(id) => (self.qubit(*id) >> shot_idx) & 1,
                crate::circuit::QubitOrBit::Bit(id) => (self.bit(*id) >> shot_idx) & 1,
            };
            v.set_bit(i, bit_val != 0);
        }
        v
    }
}
}

#[cfg(test)]
pub(crate) use simulator::Simulator;
