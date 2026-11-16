//! Bounded test-only native sink. No effect unless this thread installs it.
use super::builder::G;
use crate::circuit::{Op, OperationType as K, QubitId, NO_QUBIT};
use crate::sim::SimStats;
use sha3::{digest::{ExtendableOutput, XofReader}, Digest, Keccak256, Shake256};
use std::cell::RefCell;

pub(crate) const WIDTH:usize=660;
pub(crate) const BITS:usize=10002;
pub(crate) const CHUNK:usize=4096;
pub(crate) const RECIPE_CAP:usize=2_000_000;
pub(crate) const PRODUCER_OP_CAP:u64=2_000_000_000;
pub(crate) const RECORD_OP_CAP:u64=8_000_000;
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Image {pub q:Vec<u64>,pub bits:Vec<u64>,pub phase:u64}
impl Image {
    pub fn zero()->Self {Self{q:vec![0;WIDTH],bits:vec![0;BITS],phase:0}}
    pub fn signed_eq(&self, other:&Self, label:&str) {
        for(w,(a,b))in self.q.iter().zip(&other.q).enumerate(){assert_eq!(a,b,"{label}: q{w}, mask {:016x}",a^b);}
        assert_eq!(self.phase,other.phase,"{label}: phase mask {:016x}",self.phase^other.phase);
    }
}
struct Rng {inner:sha3::Shake256Reader,bytes:u64}
impl XofReader for Rng {fn read(&mut self,out:&mut[u8]) {self.bytes+=out.len()as u64;self.inner.read(out);}}
#[derive(Clone,Debug)]
pub(crate) struct Receipt {
    pub ops:u64,pub counts:[u64;18],pub audits:[u64;2],pub rng_bytes:u64,
    pub operation_hash:String,pub phase:u64,pub stats:SimStats,
}
#[derive(Debug)]
pub(crate) struct NativeFailure {pub op:u64,pub wire:u64,pub bad_mask:u64,pub compute:bool,pub rng_bytes:u64,pub prefix_hash:String}
struct Driver {
    image:Image,rng:Rng,stats:SimStats,stack:Vec<u64>,condition:u64,
    buffer:Vec<Op>,hash:Keccak256,ops:u64,counts:[u64;18],audits:[u64;2],cap:u64,forbidden:Option<QubitId>,hash_only:bool,
}
impl Driver {
    fn flush(&mut self) {
        if self.buffer.is_empty(){return;}
        if self.hash_only{self.buffer.clear();return;}
        let mut native=native::Simulator{
            phase:self.image.phase,qubits:std::mem::take(&mut self.image.q),
            bits:std::mem::take(&mut self.image.bits),xof:&mut self.rng,stats:self.stats,
            condition_stack:std::mem::take(&mut self.stack),current_base_condition:self.condition,
        };
        native.apply_iter(self.buffer.iter());
        self.image.q=native.qubits;self.image.bits=native.bits;self.image.phase=native.phase;
        self.stats=native.stats;self.stack=native.condition_stack;self.condition=native.current_base_condition;
        self.buffer.clear();
    }
    fn push(&mut self,op:&Op) {
        assert!(self.ops<self.cap,"K1_RESOURCE operation cap {}",self.cap);
        op.validate();
        if let Some(q)=self.forbidden{assert!(![op.q_target,op.q_control1,op.q_control2].contains(&q),"fourth-role operand {}",q.0);}
        assert!(op.q_target==NO_QUBIT||op.q_target.0<WIDTH as u64);
        assert!(op.q_control1==NO_QUBIT||op.q_control1.0<WIDTH as u64);
        assert!(op.q_control2==NO_QUBIT||op.q_control2.0<WIDTH as u64);
        for b in [op.c_target,op.c_condition] {assert!(b==crate::circuit::NO_BIT||b.0<BITS as u64,"classical capacity");}
        self.hash.update([op.kind as u8]);
        for x in [op.q_control2.0,op.q_control1.0,op.q_target.0,op.c_target.0,op.c_condition.0,op.r_target.0] {self.hash.update(x.to_le_bytes());}
        self.ops+=1;self.counts[op.kind as usize]+=1;
        self.buffer.push(*op);if self.buffer.len()==CHUNK{self.flush();}
    }
    fn gate(&mut self,g:G,inverse:bool) {
        if self.hash_only{return;}
        if let G::AndC(a,b,t)|G::AndU(a,b,t)=g {
            self.flush();let compute=matches!(g,G::AndC(..))!=inverse;
            let expected=if compute{0}else{self.image.q[a.0 as usize]&self.image.q[b.0 as usize]};
            let bad=(self.image.q[t.0 as usize]^expected)&self.condition;
            if bad!=0 {let failure=NativeFailure{op:self.ops,wire:t.0,bad_mask:bad,compute,rng_bytes:self.rng.bytes,prefix_hash:format!("{:x}",self.hash.clone().finalize())};eprintln!("K1_NATIVE_FAILURE {failure:?}");std::panic::panic_any(failure);}
            self.audits[usize::from(!compute)]+=1;
        }
    }
    fn receipt(&mut self)->Receipt {
        self.flush();assert!(self.stack.is_empty()&&self.condition==u64::MAX,"capture inside classical condition");
        Receipt{ops:self.ops,counts:self.counts,audits:self.audits,rng_bytes:self.rng.bytes,
            operation_hash:format!("{:x}",self.hash.clone().finalize()),phase:self.image.phase,stats:self.stats}
    }
}
thread_local! {static ACTIVE:RefCell<Option<Driver>>=const{RefCell::new(None)};}
pub(crate) struct Scope;
impl Drop for Scope {fn drop(&mut self){ACTIVE.with(|d|{d.borrow_mut().take();});}}
pub(crate) fn begin(image:Image,seed:&[u8],cap:u64)->Scope {
    assert_eq!((image.q.len(),image.bits.len()),(WIDTH,BITS));
    let mut hash=Shake256::default();sha3::digest::Update::update(&mut hash,seed);
    ACTIVE.with(|d|{let mut d=d.borrow_mut();assert!(d.is_none());*d=Some(Driver{image,
        rng:Rng{inner:hash.finalize_xof(),bytes:0},stats:SimStats::default(),stack:vec![],condition:u64::MAX,
        buffer:Vec::with_capacity(CHUNK),hash:Keccak256::new(),ops:0,counts:[0;18],audits:[0;2],cap,forbidden:None,hash_only:false});});Scope
}
pub(crate) fn hash_only()->Scope {let scope=begin(Image::zero(),b"hash-only",RECORD_OP_CAP);ACTIVE.with(|a|a.borrow_mut().as_mut().unwrap().hash_only=true);scope}
pub(crate) fn forbid(q:QubitId){ACTIVE.with(|a|a.borrow_mut().as_mut().unwrap().forbidden=Some(q));}
pub(crate) fn values(ports:&[QubitId])->Vec<u64>{ACTIVE.with(|a|{let mut a=a.borrow_mut();let a=a.as_mut().unwrap();a.flush();assert!(a.stack.is_empty());ports.iter().map(|q|a.image.q[q.0 as usize]).collect()})}
pub(crate) fn snapshot()->(Image,Receipt) {
    ACTIVE.with(|d|{let mut d=d.borrow_mut();let a=d.as_mut().expect("native sink absent");let r=a.receipt();(a.image.clone(),r)})
}
pub(crate) fn finish(scope:Scope)->(Image,Receipt) {
    let result=ACTIVE.with(|d|{let mut a=d.borrow_mut().take().expect("native sink absent");let r=a.receipt();(a.image,r)});
    drop(scope);result
}
pub(crate) fn observe_op(op:&Op)->bool {
    ACTIVE.with(|d|{let mut d=d.borrow_mut();if let Some(a)=d.as_mut(){a.push(op);true}else{false}})
}
pub(crate) fn observe_gate(g:G,inverse:bool) {
    ACTIVE.with(|d|{if let Some(a)=d.borrow_mut().as_mut(){a.gate(g,inverse);}});
}
pub(crate) fn record_capacity(len:usize,capacity:usize) {
    ACTIVE.with(|d|if d.borrow().is_some(){assert!(len<RECIPE_CAP&&capacity<=2*RECIPE_CAP,"K1_RESOURCE recipe cap");});
}
/// Source-bound operations pass through B::raw_direct; this helper is only for
/// exact native adapter differential controls, never candidate emission.
fn replay_controls(ops:&[Op],input:Image,seed:&[u8])->(Image,Receipt) {
    let scope=begin(input,seed,1000);for op in ops{assert!(observe_op(op));}finish(scope)
}
pub(crate) fn differential_controls() {
    use crate::circuit::{BitId,NO_BIT};
    let q=|n|QubitId(n);let bit=BitId(0);
    let ops=[
        Op{kind:K::BitStore1,c_target:bit,..Op::empty()},
        Op{kind:K::PushCondition,c_condition:bit,..Op::empty()},
        Op{kind:K::X,q_target:q(0),..Op::empty()},
        Op{kind:K::Hmr,q_target:q(0),c_target:BitId(1),..Op::empty()},
        Op{kind:K::PushCondition,c_condition:BitId(1),..Op::empty()},
        Op{kind:K::CCX,q_control1:q(1),q_control2:q(2),q_target:q(3),..Op::empty()},
        Op{kind:K::CZ,q_control1:q(1),q_target:q(3),..Op::empty()},
        Op{kind:K::PopCondition,..Op::empty()},
        Op{kind:K::BitInvert,c_target:bit,..Op::empty()},
        Op{kind:K::CX,q_control1:q(2),q_target:q(4),c_condition:bit,..Op::empty()},
        Op{kind:K::PopCondition,..Op::empty()},
        Op{kind:K::Swap,q_control1:q(1),q_target:q(4),..Op::empty()},
        Op{kind:K::CCZ,q_control1:q(1),q_control2:q(2),q_target:q(3),..Op::empty()},
        Op{kind:K::R,q_target:q(4),..Op::empty()},
        Op{kind:K::Z,q_target:q(1),c_condition:NO_BIT,..Op::empty()},
        Op{kind:K::Neg,..Op::empty()},
        Op{kind:K::BitStore0,c_target:bit,..Op::empty()},
        Op{kind:K::Register,r_target:crate::circuit::RegisterId(0),..Op::empty()},
        Op{kind:K::AppendToRegister,r_target:crate::circuit::RegisterId(0),q_target:q(1),..Op::empty()},
        Op{kind:K::DebugPrint,..Op::empty()},
    ];
    fn input(case:u64)->Image{let mut image=Image::zero();for(j,x)in image.q.iter_mut().enumerate(){*x=case.rotate_left(j as u32)^0x962567b33f81050a_u64.rotate_right(j as u32);}
        image.phase=case^0xaaff55aa55ff00aa;image}
    for case in 0..128u64 {
        let initial=input(case);
        let seed=case.to_le_bytes();let mut h=Shake256::default();sha3::digest::Update::update(&mut h,&seed);
        let mut rng=Rng{inner:h.finalize_xof(),bytes:0};let mut sim=crate::sim::Simulator::new(WIDTH,BITS,&mut rng);
        sim.qubits=initial.q;sim.bits=initial.bits;sim.phase=initial.phase;
        sim.apply_iter(ops.iter());let expected=Image{q:sim.qubits,bits:sim.bits,phase:sim.phase};let expected_stats=sim.stats;
        let(result,receipt)=replay_controls(&ops,input(case),&seed);
        assert_eq!(result,expected);assert_eq!(receipt.rng_bytes,rng.bytes);assert_eq!(receipt.stats,expected_stats);drop(result);
        // Every split is exercised, including both PUSH scopes: force a flush
        // while retaining the scope state in the literal native dispatcher.
        for split in 1..ops.len(){let scope=begin(input(case),&seed,1000);
            for op in &ops[..split]{assert!(observe_op(op));}
            ACTIVE.with(|d|d.borrow_mut().as_mut().unwrap().flush());
            for op in &ops[split..]{assert!(observe_op(op));}
            ACTIVE.with(|d|{let mut d=d.borrow_mut();let a=d.as_mut().unwrap();a.flush();assert_eq!(a.stats,expected_stats);});
            let(result,receipt)=finish(scope);assert_eq!(result,expected);assert_eq!(receipt.rng_bytes,rng.bytes);
        }
    }
    println!("K1_NATIVE_STREAM_CONTROLS cases=128 split_points=19 native_plays=2688 op_visits=53760 all_wire_phase_classical_rng_stats=PASS");
}

// The dispatcher below is the literal bound native sim.rs dispatcher.
// Condition-stack initialization/storage alone persists between chunks.
mod native {
    use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT};
    use crate::sim::SimStats;
    pub(super) struct Simulator<'a, R: sha3::digest::XofReader> {
        pub phase:u64, pub qubits:Vec<u64>, pub bits:Vec<u64>,
        pub xof:&'a mut R, pub stats:SimStats,
        pub condition_stack:Vec<u64>, pub current_base_condition:u64,
    }
    impl<R:sha3::digest::XofReader> Simulator<'_, R> {
        #[inline(always)] fn qubit(&self,q:QubitId)->u64 {self.qubits[q.0 as usize]}
        #[inline(always)] fn qubit_mut(&mut self,q:QubitId)->&mut u64 {&mut self.qubits[q.0 as usize]}
        #[inline(always)] fn bit(&self,b:BitId)->u64 {self.bits[b.0 as usize]}
        #[inline(always)] fn bit_mut(&mut self,b:BitId)->&mut u64 {&mut self.bits[b.0 as usize]}
    pub fn apply_iter<'b>(&mut self, ops: impl Iterator<Item = &'b Op>) {

        let mut condition_stack = std::mem::take(&mut self.condition_stack);
        let mut current_base_condition = self.current_base_condition;

        for op in ops {
            let mut cond = current_base_condition;
            if op.c_condition != NO_BIT {
                cond &= self.bit(op.c_condition);
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
        self.condition_stack = condition_stack;
        self.current_base_condition = current_base_condition;
    }

    }
}
