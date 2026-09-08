//! Actual emitted sequence, bounded memory, independent development seed.
//! This is NOT the official Fiat-Shamir acceptance procedure.
use crate::circuit::{Op,OperationType as K,QubitId,QubitOrBit,BitId};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{Shake256,digest::{Update,ExtendableOutput,XofReader}};
pub(crate) struct Check {
    sim:Simulator<'static,sha3::Shake256Reader>, expected:Vec<(U256,U256)>, offsets:Vec<(U256,U256)>,
    ops:usize, initial_ops:usize, started:std::time::Instant, regs:Vec<Vec<QubitOrBit>>,
}
impl Check {
    pub fn new(tx:&[super::trailmix_port::circuit::QReg],ty:&[super::trailmix_port::circuit::QReg],ox:&[super::trailmix_port::circuit::Cbit],oy:&[super::trailmix_port::circuit::Cbit],initial_ops:usize)->Self {
        let curve=super::compact_check::secp256k1();
        let mut seed=Shake256::default();seed.update(b"Q799-independent-whole-stream-sprint-v2");
        if let Ok(s)=std::env::var("SPRINT_STREAM_SEED"){seed.update(s.as_bytes());}
        let reader=Box::leak(Box::new(seed.finalize_xof()));
        let mut sim=Simulator::new(1024,1_000_000,reader);let mut expected=Vec::new();let mut offsets=Vec::new();
        let regs:Vec<Vec<QubitOrBit>>=vec![tx.iter().map(|q|QubitOrBit::Qubit(QubitId(q.id() as u64))).collect(),ty.iter().map(|q|QubitOrBit::Qubit(QubitId(q.id() as u64))).collect(),ox.iter().map(|q|QubitOrBit::Bit(BitId(q.raw() as u64))).collect(),oy.iter().map(|q|QubitOrBit::Bit(BitId(q.raw() as u64))).collect()];
        for lane in 0..64 {
            let mut a=[0u8;32];let mut b=[0u8;32];sim.xof.read(&mut a);sim.xof.read(&mut b);
            let t=curve.mul(curve.gx,curve.gy,U256::from_le_bytes(a));let o=curve.mul(curve.gx,curve.gy,U256::from_le_bytes(b));
            assert_ne!(t.0,o.0);assert_ne!(t,(U256::ZERO,U256::ZERO));assert_ne!(o,(U256::ZERO,U256::ZERO));
            expected.push(curve.add(t.0,t.1,o.0,o.1));offsets.push(o);
            for (r,v) in regs.iter().zip([t.0,t.1,o.0,o.1]){sim.set_register(r,v,lane);}
        }
        eprintln!("SPRINT_STREAM_START independent_shots=64 initial_ops={initial_ops}; no stream retained");
        Self{sim,expected,offsets,ops:0,initial_ops,started:std::time::Instant::now(),regs:Vec::new()}
    }
    pub fn apply(&mut self,ops:&[Op]) {
        assert!(!ops.iter().any(|o|matches!(o.kind,K::PushCondition|K::PopCondition)));
        for op in ops {if op.kind==K::AppendToRegister {
            let r=op.r_target.0 as usize;while self.regs.len()<=r{self.regs.push(Vec::new());}
            self.regs[r].push(if op.q_target.0!=u64::MAX{QubitOrBit::Qubit(op.q_target)}else{QubitOrBit::Bit(op.c_target)});
        }}
        self.sim.apply_iter(ops.iter());self.ops+=ops.len();
    }
    pub fn finish(self,b:&super::B) {
        eprintln!("SPRINT_MEMORY_ACCOUNT ops={} op_bytes={} classical_bits={} classical_bytes={} physical_qubits={}",b.counted_ops,b.counted_ops*std::mem::size_of::<Op>(),b.next_bit,b.next_bit as u64*8,b.next_qubit);
        assert_eq!(self.ops+self.initial_ops,b.counted_ops,"real stream coverage");
        assert_eq!(self.regs.len(),4);let regs=&self.regs;let mut failures=0;
        for lane in 0..64 {
            let got=(self.sim.get_register(&regs[0],lane),self.sim.get_register(&regs[1],lane));
            if got!=self.expected[lane]{failures+=1;eprintln!("SPRINT_STREAM_MISMATCH lane={lane} got={got:?} expected={:?}",self.expected[lane]);}
            assert_eq!((self.sim.get_register(&regs[2],lane),self.sim.get_register(&regs[3],lane)),self.offsets[lane]);
        }
        let output:std::collections::BTreeSet<_>=regs.iter().flat_map(|r|r.iter()).filter_map(|q|if let QubitOrBit::Qubit(q)=q{Some(q.0 as usize)}else{None}).collect();
        let garbage=self.sim.qubits.iter().enumerate().filter(|(q,v)|!output.contains(q)&&**v!=0).count();
        eprintln!("SPRINT_STREAM_RESULT shots=64 peak={} physical={} simulated_ops={} structural_T={} executed_average_T={} classical_failures={failures} phase={:#018x} dirty_ancillas={garbage} elapsed={:.1}; independent development seed, not official acceptance",b.peak_qubits,b.next_qubit,self.ops,b.counted_kind_ops[K::CCX as usize]+b.counted_kind_ops[K::CCZ as usize],self.sim.stats.toffoli_gates/64,self.sim.phase,self.started.elapsed().as_secs_f64());
        assert_eq!(failures,0);assert_eq!(self.sim.phase,0);assert_eq!(garbage,0);
    }
}
