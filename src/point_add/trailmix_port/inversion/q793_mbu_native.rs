//! Native test adapter: invoke on unchanged reachable rows in C1/general/step
//! checkpoint tests. No input corpus is synthesized or assumed here.
use crate::{circuit::{Op,OperationType as K,QubitId,BitId},sim::Simulator};
use sha3::digest::XofReader;
struct Outcome(u8);
impl XofReader for Outcome { fn read(&mut self,bytes:&mut[u8]) {bytes.fill(self.0);} }

pub(crate) fn check(before:&[u64], original:&[Op], phase_body:&[Op], sign:QubitId)->u32 {
    assert!(original.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
    assert!(phase_body.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX|K::Neg|K::Z|K::CZ)));
    for o in original.iter().chain(phase_body) {o.validate();}
    let index=sign.0 as usize;
    let mut expected=before.to_vec();expected[index]=0;
    // Establish the pure-erasure interface on the ACTUAL original wrapper,
    // rather than inferring zero from how its logical register was allocated.
    let mut rng=Outcome(0);let mut base=Simulator::new(before.len(),0,&mut rng);
    base.qubits.copy_from_slice(before);base.apply_iter(original.iter());
    assert_eq!(base.qubits,expected,"original wrapper is not pure reachable Sign cleanup");
    assert_eq!(base.phase,0);
    // The phase body must itself preserve every wire, including zero Sign,
    // while computing exactly the original incoming Sign as a diagonal phase.
    let mut rng=Outcome(0);let mut diag=Simulator::new(before.len(),0,&mut rng);
    diag.qubits.copy_from_slice(&expected);diag.apply_iter(phase_body.iter());
    assert_eq!(diag.qubits,expected,"phase body did not restore chart/DATA/helpers");
    assert_eq!(diag.phase,before[index],"phase body computes wrong Sign predicate");
    let mut h=Op::empty();h.kind=K::Hmr;h.q_target=sign;h.c_target=BitId(0);
    // Match the actual production representation: one classical condition
    // on every phase operation, not a simulator condition-stack shortcut.
    let packet:Vec<_>=std::iter::once(h).chain(phase_body.iter().copied().map(|mut op|{op.c_condition=BitId(0);op.validate();op})).collect();
    for outcome in [0,255] {
        let mut rng=Outcome(outcome);let mut sim=Simulator::new(before.len(),1,&mut rng);
        sim.qubits.copy_from_slice(before);
        // Single apply_iter call: condition stack must not cross call boundaries.
        sim.apply_iter(packet.iter());
        assert_eq!(sim.qubits,expected,"HMR correction changed output or dirty cargo");
        assert_eq!(sim.phase,0,"HMR correction leaves phase garbage");
        assert_eq!(sim.bits[0],if outcome==0{0}else{u64::MAX});
    }
    before[index].count_ones()
}
