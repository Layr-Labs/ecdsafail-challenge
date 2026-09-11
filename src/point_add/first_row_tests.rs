//! Independent row-image and integer-square tests, including every reset.
use super::{erase_first_row, row_addsub, tri_square, Builder};
use crate::circuit::{Op, OperationType, QubitId, NO_BIT};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::digest::XofReader;

struct Draws(u64);
impl XofReader for Draws {
    fn read(&mut self, dst: &mut [u8]) {
        for chunk in dst.chunks_mut(8) {
            self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
            z ^= z >> 31;
            chunk.copy_from_slice(&z.to_le_bytes()[..chunk.len()]);
        }
    }
}
fn dims(ops: &[Op]) -> (usize, usize) {
    let mut q = 1;
    let mut b = 1;
    for op in ops {
        for id in [op.q_control1.0, op.q_control2.0, op.q_target.0] {
            if id != u64::MAX { q = q.max(id as usize + 1); }
        }
        for id in [op.c_target.0, op.c_condition.0] {
            if id != u64::MAX { b = b.max(id as usize + 1); }
        }
    }
    (q, b)
}
fn run(ops: &[Op], inputs: &[(&[QubitId], Vec<U512>)], seed: u64) -> Vec<u64> {
    let (q, b) = dims(ops);
    let mut draws = Draws(seed);
    let mut sim = Simulator::new(q, b, &mut draws);
    for (reg, values) in inputs {
        for (lane, value) in values.iter().enumerate() {
            for (i, wire) in reg.iter().enumerate() {
                if value.bit(i) { sim.qubits[wire.0 as usize] |= 1 << lane; }
            }
        }
    }
    let mut base = u64::MAX;
    let mut stack = Vec::new();
    for op in ops {
        let cond = base & if op.c_condition == NO_BIT { u64::MAX } else { sim.bits[op.c_condition.0 as usize] };
        match op.kind {
            OperationType::PushCondition => { stack.push(base); base = cond; }
            OperationType::PopCondition => { base = stack.pop().unwrap(); }
            _ => {
                if op.kind == OperationType::R {
                    assert_eq!(sim.qubits[op.q_target.0 as usize] & cond, 0, "dirty reset");
                }
                // Apply the original native operation under the effective condition.
                if base == u64::MAX { sim.apply_iter(std::iter::once(op)); }
                else {
                    let mut masked = *op;
                    let private = sim.bits.len();
                    sim.bits.push(cond);
                    masked.c_condition = crate::circuit::BitId(private as u64);
                    sim.apply_iter(std::iter::once(&masked));
                    sim.bits.pop();
                }
            }
        }
    }
    assert!(stack.is_empty());
    assert_eq!(sim.phase, 0, "uncorrected phase");
    sim.qubits
}
fn check_reg(q: &[u64], reg: &[QubitId], values: &[U512]) {
    for (lane, value) in values.iter().enumerate() {
        for (i, wire) in reg.iter().enumerate() {
            assert_eq!((q[wire.0 as usize] >> lane) & 1, u64::from(value.bit(i)), "lane={lane} bit={i}");
        }
    }
}
fn samples(width: usize, start: usize) -> Vec<U512> {
    let mask = (U512::from(1) << width) - U512::from(1);
    if width <= 8 { return (0..64).map(|lane| U512::from((start + lane) % (1 << width))).collect(); }
    let mut rng = Draws(0x12345678 + start as u64);
    (0..64).map(|lane| {
        if lane < 4 { return [U512::ZERO, U512::from(1), mask, mask - U512::from(1)][lane]; }
        let mut bytes = [0u8; 64];
        rng.read(&mut bytes);
        U512::from_le_bytes(bytes) & mask
    }).collect()
}
#[test]
fn first_row_independent_images_and_zero_toffolis() {
    for k in (1..=8).chain([31, 32, 33, 63, 64, 65, 127, 128]) {
        let mut circ = Builder::new();
        let ctrl = circ.alloc_qubit();
        let a = circ.alloc_qubits(k);
        let acc = circ.alloc_qubits(k + 1);
        erase_first_row(&mut circ, ctrl, &a, &acc);
        let ops = circ.take_ops();
        assert!(!ops.iter().any(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)));
        assert_eq!(dims(&ops).0, 2*k+2, "no new quantum scratch");
        for control in [0usize, 1] {
            for batch in 0..if k <= 8 { (1usize << k).div_ceil(64) } else { 4 } {
                let values = samples(k, batch * 64);
                let c = U512::from(1 - control);
                let row: Vec<_> = values.iter().map(|&a| (a+c*((U512::from(1)<<k)-U512::from(1))) ^ (c*((U512::from(1)<<(k+1))-U512::from(1)))).collect();
                let controls = vec![U512::from(control); 64];
                for seed in [0, 1, 0xdeadbeef] {
                    let q = run(&ops, &[(&[ctrl], controls.clone()), (&a, values.clone()), (&acc, row.clone())], seed);
                    check_reg(&q, &[ctrl], &controls);
                    check_reg(&q, &a, &values);
                    check_reg(&q, &acc, &vec![U512::ZERO; 64]);
                }
            }
        }
        let mut old = Builder::new();
        let ctrl = old.alloc_qubit();
        let a = old.alloc_qubits(k);
        let acc = old.alloc_qubits(k+1);
        row_addsub(&mut old, ctrl, &a, &acc, true);
        assert_eq!(old.take_ops().iter().filter(|o| o.kind == OperationType::CCX).count(), k);
    }
}
#[test]
fn first_row_integer_square_forward_and_independent_inverse() {
    // Does not use or initialize the recursive policy's OnceLocks.
    for m in (2..=8).chain([32, 64, 65, 128, 129]) {
        for inverse in [false, true] {
            let mut circ = Builder::new();
            let x = circ.alloc_qubits(m);
            let product = circ.alloc_qubits(2*m);
            tri_square(&mut circ, &x, &product, inverse);
            let ops = circ.take_ops();
            for batch in 0..if m <= 8 { (1usize << m).div_ceil(64) } else { 4 } {
                let values = samples(m, batch * 64);
                let squares: Vec<_> = values.iter().map(|&v| v*v).collect();
                for seed in [0, 1, 0xdeadbeef] {
                    let q = run(&ops, &[(&x, values.clone()), (&product, if inverse { squares.clone() } else { vec![U512::ZERO;64] })], seed);
                    check_reg(&q, &x, &values);
                    check_reg(&q, &product, &if inverse { vec![U512::ZERO;64] } else { squares.clone() });
                    for value in &q[3*m..] { assert_eq!(*value, 0, "dirty square scratch"); }
                }
            }
        }
    }
}
