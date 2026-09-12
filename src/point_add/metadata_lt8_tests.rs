//! Small native lease tests, not an Algorithm3 reachability test.
use super::*;
use crate::circuit::{BitId, NO_BIT};
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Outcomes(u8);
impl XofReader for Outcomes {
    fn read(&mut self, b: &mut [u8]) {
        b.fill(self.0);
    }
}
fn gate(kind: OperationType, a: Option<u64>, b: Option<u64>, target: u64) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    op.q_target = QubitId(target);
    if let Some(a) = a {
        op.q_control1 = QubitId(a);
    }
    if let Some(b) = b {
        op.q_control2 = QubitId(b);
    }
    op
}
fn mcx(ops: &mut Vec<Op>, controls: &[u64], target: u64, scratch: &[u64]) {
    use OperationType::*;
    match controls.len() {
        0 => ops.push(gate(X, None, None, target)),
        1 => ops.push(gate(CX, Some(controls[0]), None, target)),
        2 => ops.push(gate(CCX, Some(controls[0]), Some(controls[1]), target)),
        n => {
            assert!(scratch.len() >= n - 2);
            ops.push(gate(CCX, Some(controls[0]), Some(controls[1]), scratch[0]));
            for i in 2..n - 1 {
                ops.push(gate(
                    CCX,
                    Some(controls[i]),
                    Some(scratch[i - 2]),
                    scratch[i - 1],
                ));
            }
            ops.push(gate(
                CCX,
                Some(controls[n - 1]),
                Some(scratch[n - 3]),
                target,
            ));
            for i in (2..n - 1).rev() {
                ops.push(gate(
                    CCX,
                    Some(controls[i]),
                    Some(scratch[i - 2]),
                    scratch[i - 1],
                ));
            }
            ops.push(gate(CCX, Some(controls[0]), Some(controls[1]), scratch[0]));
        }
    }
}
fn pool(ops: &mut Vec<Op>) {
    use OperationType::*;
    ops.push(gate(CCX, Some(9), Some(10), 12));
    ops.push(gate(CX, Some(12), None, 11));
    let mut h = gate(Hmr, None, None, 12);
    h.c_target = BitId(0);
    ops.push(h);
    let mut z = gate(CZ, Some(9), None, 10);
    z.c_condition = BitId(0);
    ops.push(z);
}
fn program() -> Vec<Op> {
    use OperationType::*;
    let mut out = Vec::new();
    pool(&mut out);
    let mut plus_two = Vec::new();
    for bit in (2..9).rev() {
        mcx(
            &mut plus_two,
            &(1..bit).collect::<Vec<_>>(),
            bit,
            &[13, 14, 15, 16, 17],
        );
    }
    plus_two.push(gate(X, None, None, 1));
    out.extend_from_slice(&plus_two);
    out.push(gate(CX, Some(8), None, 11));
    out.push(gate(Z, None, None, 8));
    out.extend(plus_two.into_iter().rev());
    pool(&mut out);
    for op in &out {
        op.validate();
    }
    out
}
fn observed_reference<R: XofReader>(
    s: &mut Simulator<'_, R>,
    ops: &[Op],
    lease: Lease,
    mask: u64,
) -> bool {
    let mut valid = true;
    for op in ops {
        let cond = if op.c_condition == NO_BIT {
            u64::MAX
        } else {
            s.bit(op.c_condition)
        };
        let other = match lease.role(op) {
            1 => Some(lease.pool),
            2 => Some(lease.high),
            3 => return false,
            _ => None,
        };
        if let Some(q) = other {
            if s.qubit(QubitId(q)) & cond & mask != 0 {
                valid = false;
            }
        }
        s.apply_iter(std::iter::once(op));
    }
    valid
}
#[test]
fn metadata_lt8_leased_ninth_bit_native_all_low_inputs() {
    let lease = Lease { high: 8, pool: 12 };
    let old = program();
    let mut new = old.clone();
    let count = coalesce(&mut new, lease).unwrap();
    assert!(count.high_ops > 0 && count.pool_ops > 0 && count.ownership_switches >= 2);
    assert_eq!(old.len(), new.len());
    let mut checked = 0;
    for outcome in [0, 255] {
        let (mut a, mut b) = (Outcomes(outcome), Outcomes(outcome));
        let (mut oldsim, mut newsim) =
            (Simulator::new(18, 1, &mut a), Simulator::new(17, 1, &mut b));
        for first in (0..2048usize).step_by(64) {
            oldsim.clear_for_shot();
            newsim.clear_for_shot();
            oldsim.phase = 0x9635ca6996c3a55a;
            newsim.phase = oldsim.phase;
            for lane in 0..64 {
                let input = first + lane;
                for bit in 0..8 {
                    if (input >> bit) & 1 != 0 {
                        oldsim.qubits[bit] |= 1u64 << lane;
                        newsim.qubits[bit] |= 1u64 << lane;
                    }
                }
                for (bit, q) in [(8, 9), (9, 10), (10, 11)] {
                    if (input >> bit) & 1 != 0 {
                        oldsim.qubits[q] |= 1u64 << lane;
                        newsim.qubits[lease.map(QubitId(q as u64)).0 as usize] |= 1u64 << lane;
                    }
                }
            }
            assert!(observed_reference(&mut oldsim, &old, lease, u64::MAX));
            newsim.apply_iter(new.iter());
            assert_eq!(oldsim.phase, newsim.phase);
            assert_eq!(oldsim.bits, newsim.bits);
            assert_eq!(oldsim.stats, newsim.stats);
            assert_eq!(oldsim.qubits[8], 0);
            assert_eq!(oldsim.qubits[12], 0);
            for q in 0..18 {
                if q != 8 {
                    assert_eq!(
                        oldsim.qubits[q],
                        newsim.qubits[lease.map(QubitId(q as u64)).0 as usize]
                    );
                }
            }
            for lane in 0..64 {
                let input = first + lane;
                let carry = (input & 255) >= 254;
                assert_eq!(
                    (oldsim.qubits[11] >> lane) & 1,
                    ((input >> 10) & 1) as u64 ^ u64::from(carry)
                );
                assert_eq!(
                    (oldsim.phase >> lane) & 1,
                    (0x9635ca6996c3a55au64 >> lane) & 1 ^ u64::from(carry)
                );
            }
            checked += 64;
        }
    }
    eprintln!("METADATA_LT8_LEASE_NATIVE PASS cases={checked}; meaningful ninth-bit carry/phase, dirty-data product pool, both HMR outcomes, zero lease interfaces, exact operation/stat count, one fewer physical wire");
}
#[test]
fn metadata_lt8_alias_and_nonzero_lease_falsifiers() {
    let lease = Lease { high: 8, pool: 12 };
    let bad = vec![gate(OperationType::CX, Some(8), None, 12)];
    let mut copy = bad.clone();
    assert!(coalesce(&mut copy, lease).is_err());
    assert_eq!(copy, bad);
    let mut rng = Outcomes(0);
    let mut sim = Simulator::new(18, 1, &mut rng);
    sim.qubits[8] = 1;
    assert!(!observed_reference(&mut sim, &program(), lease, 1));
}
