//! Exact source-bound classical control; independent of inputs and tail nonce.
//! The source-only prefix induction proves q706 = bit773 XOR bit774 here.
//! Both classical bits and all quantum wires retain their original updates.
use crate::circuit::{Op, OperationType as K, BitId, QubitId};
use sha3::{Digest, Sha3_256};
const INDEX: usize = 5_387_927;
const COUNT: usize = 17_889_530;
const HASH: &str = "b9c8046798d5f67aaf5426e20d7d601d500f618e5e06a61f9242af9a2574360c";
const NO: u64 = u64::MAX;
fn hash(v: &[Op]) -> String {
    let mut h = Sha3_256::new();
    for o in v { for x in [o.kind as u64, o.q_control2.0, o.q_control1.0,
        o.q_target.0, o.c_target.0, o.c_condition.0, o.r_target.0] {
        h.update(x.to_le_bytes());
    }}
    format!("{:x}", h.finalize())
}
fn bind(v: &[Op], count: usize, expected: &str) {
    assert_eq!(v.len(), count, "classical XOR source count");
    assert_eq!(hash(v), expected, "classical XOR source hash");
}
fn replacement(g: Op, a: u64, b: u64) -> [Op; 2] {
    assert_eq!(g.kind, K::CCX);
    assert_eq!(g.c_condition.0, NO);
    let mut x = Op::empty(); x.kind = K::CX;
    x.q_control1 = g.q_control1; x.q_target = g.q_target;
    x.c_condition = BitId(a);
    let mut y = x; y.c_condition = BitId(b);
    [x, y]
}
pub(super) fn run(mut v: Vec<Op>) -> Vec<Op> {
    bind(&v, COUNT, HASH);
    let g = v[INDEX];
    assert_eq!([g.kind as u64, g.q_control2.0, g.q_control1.0,
        g.q_target.0, g.c_target.0, g.c_condition.0, g.r_target.0],
        [13, 706, 816, 703, NO, NO, NO]);
    v.splice(INDEX..INDEX + 1, replacement(g, 773, 774));
    v
}
#[cfg(test)] mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed(u8); impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
    }
    #[test] fn exhaustive_dirty_target_phase_and_rng_control() {
        for p in [0u8, 255, 0xa5, 0x5a] { for input in 0u64..16 {
            let mut g=Op::empty();g.kind=K::CCX;g.q_control2=QubitId(0);
            g.q_control1=QubitId(1);g.q_target=QubitId(2);
            let out=replacement(g,0,1);
            let mut ra=Fixed(p);let mut rb=Fixed(p);
            let mut a=Simulator::new(3,2,&mut ra);
            let mut b=Simulator::new(3,2,&mut rb);
            let (u,v,y,z)=(input&1,input>>1&1,input>>2&1,input>>3&1);
            a.qubits=vec![u^v,y,z];a.bits=vec![u,v];a.phase=p as u64;
            b.qubits.clone_from(&a.qubits);b.bits.clone_from(&a.bits);b.phase=a.phase;
            a.apply_iter([g].iter());b.apply_iter(out.iter());
            assert_eq!(a.qubits,b.qubits);assert_eq!(a.bits,b.bits);
            assert_eq!(a.phase,b.phase);assert_eq!(a.stats.toffoli_gates,64);
            assert_eq!(b.stats.toffoli_gates,0);
        }}
    }
    #[test] fn source_binding_includes_all_gate_fields() {
        let mut g=Op::empty();g.kind=K::X;g.q_target=QubitId(0);
        bind(&[g],1,&hash(&[g]));let h=hash(&[g]);g.c_condition=BitId(0);
        assert_ne!(h,hash(&[g]));
    }
    #[test] #[should_panic(expected="source hash")]
    fn source_binding_rejects_changed_wire() {
        let mut g=Op::empty();g.kind=K::X;g.q_target=QubitId(0);
        let h=hash(&[g]);g.q_target=QubitId(1);bind(&[g],1,&h);
    }
    #[test] #[should_panic(expected="source count")]
    fn source_binding_rejects_missing_gate() { bind(&[],1,""); }
}
